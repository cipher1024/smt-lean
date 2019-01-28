
import tactic.norm_num

universes u v

def bits64 : ℕ := by apply_normed (2^64 - 1)

@[reducible]
def word64 := fin (nat.succ bits64)

def default_salt : word64 :=
⟨by apply_normed (2^64 -2578643520546668380), by norm_num [bits64,nat.succ_eq_add_one] ⟩

class hashable (α : Type u) :=
(hash_with_salt : α → word64 → word64)

export hashable(hash_with_salt)

def hash {α} [hashable α] (x : α) : word64 :=
hash_with_salt x default_salt

class hashable1 (f : Type u → Type v) :=
(lift_hash_with_salt {α : Type u} : (α → word64 → word64) → f α → word64 → word64)

export hashable1(lift_hash_with_salt)

instance hashable1.hashable (α) (f : Type u → Type v) [hashable α] [hashable1 f] : hashable (f α) :=
{ hash_with_salt := lift_hash_with_salt hash_with_salt }

namespace hashable

def combine (h1 h2 : word64) : word64 := (h1 * 16777619) + h2

instance : hashable word64 :=
{ hash_with_salt := λ salt x, combine salt x }

def nat.hash_with_salt : ℕ → word64 → word64
| n := λ salt,
if h : n < nat.succ bits64 then ⟨_,h⟩
else
  let w : word64 := combine salt ⟨n%nat.succ bits64,nat.mod_lt _ $ by norm_num [bits64,nat.succ_eq_add_one]⟩ in
  have hn : 0 < n, by { apply lt_of_lt_of_le _ (le_of_not_lt h), norm_num [bits64,nat.succ_eq_add_one] },
  have n / nat.succ bits64 < n, from nat.div_lt_self hn $ by norm_num [bits64,nat.succ_eq_add_one],
  nat.hash_with_salt (n / nat.succ bits64) w

instance unsigned.nat : hashable ℕ :=
{ hash_with_salt := λ salt n, nat.hash_with_salt n salt }

instance unsigned.hashable : hashable unsigned :=
{ hash_with_salt := λ ⟨x,h⟩, combine ⟨x,lt_trans h $ by { norm_num [unsigned_sz,bits64,nat.succ_eq_add_one] }⟩ }

instance char.hashable : hashable char :=
{ hash_with_salt := λ x, combine x.val }

def finalize : word64 × word64 → word64
| (s,l) := hash_with_salt s l

def step {α} (h : α → word64 → word64) : word64 × word64 → α → word64 × word64
| (s,l) x := (h x s, l + 1)

instance : hashable1 list :=
{ lift_hash_with_salt := λ α h arr salt, finalize $ arr.foldl (step h) (salt,0) }

instance string.hashable : hashable string :=
{ hash_with_salt := λ s, hash_with_salt s.to_list }

end hashable
namespace tactic

meta def mk_hashable_instance : tactic unit :=
do `(hashable %%t) ← target,
   refine ``( { hash_with_salt := _ } ),
   x ← intro1,
   hs ← induction x,
   hs.mmap' $ λ h,
     do { let n := to_string $ h.1.update_prefix name.anonymous,
          let vs := h.2.1,
          vs.mmap' $ λ h, focus1 $
            do { t' ← infer_type h,
                 is_def_eq t t' <|>
                   is_def_eq t' `(word64 → word64) >> refine ``(%%h ∘ _) <|>
                     refine ``(hash_with_salt %%h ∘ _) },
          refine ``(hash_with_salt %%(reflect n)),
          pure () }

@[derive_handler]
meta def hashable_derive_handler : derive_handler :=
instance_derive_handler ``hashable mk_hashable_instance tt

end tactic
namespace hashable

open name

attribute [derive hashable] name prod sum level option ulift

meta instance macro_def.hashable : hashable macro_def :=
{ hash_with_salt := λ m, hash_with_salt (expr.macro_def_name m) }

meta def expr.hash  : expr → word64 → word64
| (expr.var a_1) := hash_with_salt "var" ∘ hash_with_salt a_1
| (expr.sort a_1) := hash_with_salt "sort" ∘ hash_with_salt a_1
| (expr.const a_1 a_2) := hash_with_salt "const" ∘ hash_with_salt a_1 ∘ hash_with_salt a_2
| (expr.mvar a_1 a_2 a_3) := hash_with_salt "mvar" ∘ hash_with_salt a_1 ∘ hash_with_salt a_2 ∘ expr.hash a_3
| (expr.local_const a_1 a_2 a_3 a_4) := hash_with_salt "local_const" ∘ hash_with_salt a_1 ∘ hash_with_salt a_2 ∘ expr.hash a_4
| (expr.app a_1 a_2) := hash_with_salt "app" ∘ expr.hash a_1 ∘ expr.hash a_2
| (expr.lam a_1 a_2 a_3 a_4) := hash_with_salt "lam" ∘ expr.hash a_3 ∘ expr.hash a_4
| (expr.pi a_1 a_2 a_3 a_4) := hash_with_salt "pi" ∘ expr.hash a_3 ∘ expr.hash a_4
| (expr.elet a_1 a_2 a_3 a_4) := hash_with_salt "elet" ∘ expr.hash a_2 ∘ expr.hash a_3 ∘ expr.hash a_4
| (expr.macro a_1 a_2) := λ salt, list.foldl (λ a b, expr.hash b a) (hash_with_salt "macro" ∘ hash_with_salt a_1 $ salt) a_2

meta instance expr.hashable : hashable expr :=
{ hash_with_salt := expr.hash }

end hashable
