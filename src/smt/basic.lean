
import data.real.basic
import data.hashable
import data.tactic
import tactic
import tactic.linarith
import system.io

open io io.fs io.process parser

def sum.coe {m α} [monad m] [monad_fail m] : string ⊕ α → m α
| (sum.inl e) := monad_fail.fail $ "\n" ++ e
| (sum.inr e) := pure e

meta instance {α} : has_coe (string ⊕ α) (tactic α) := ⟨ sum.coe ⟩
instance sum.io_coe {α} : has_coe (string ⊕ α) (io α) := ⟨ sum.coe ⟩

meta instance int.reflect : has_reflect ℤ
| x :=
if x < 0 then cast undefined `(- %%(int.reflect x) : ℤ)
else if h₁ : x = 0 then cast (by rw h₁) `(0 : ℤ)
       else if h₂ : x = 1 then cast (by rw h₂) `(1 : ℤ)
       else if h₃ : x % 2 = 0 then cast undefined $ `(λ x : ℤ, bit0 x).subst (int.reflect (x / 2))
       else cast undefined `(bit1 %%(int.reflect (x / 2)) : ℤ)

meta def rat.has_reflect' : Π x : ℚ, Σ y : ℚ, Σ' h : x = y, reflected y
| ⟨x,y,h,h'⟩ := ⟨rat.mk_nat x y, by { rw [rat.num_denom',rat.mk_nat_eq] } , `(_)⟩

meta instance : has_reflect ℚ
| x :=
match rat.has_reflect' x with
| ⟨ ._, rfl, h ⟩ := h
end

namespace smt

inductive atom
| num (s : ℤ)
| dec (s : ℚ)
-- | str (s : string)
| sym (s : string)
-- | keyword (s : string)

protected meta def atom.to_string : atom → string
| (atom.num s) := to_string s
| (atom.dec s) := to_string s
-- | (atom.str s) := s
| (atom.sym s) := s
-- | (atom.keyword s) := s

meta instance atom.has_to_string : has_to_string atom :=
⟨ atom.to_string ⟩

inductive sexpr
| const : atom → sexpr
| fapp : list sexpr → sexpr

protected meta def sexpr.to_string : sexpr → string
| (sexpr.const n) := to_string n
| (sexpr.fapp args) := "( " ++ string.intercalate " " (args.map sexpr.to_string) ++ " )"

meta instance sexpr.has_to_string : has_to_string sexpr :=
⟨ sexpr.to_string ⟩

inductive type
| int | real | array (idx rng : type)

open smt.type

def type.to_string : type → string
| int := "Int"
| real := "Real"
| (array t₀ t₁) := "(Array " ++ t₀.to_string ++ " " ++ t₁.to_string ++ ")"

def string.map (f : char → char) : string → string :=
list.as_string ∘ list.map f ∘ string.to_list

protected def name := string
protected def name.to_string : smt.name → string := id

def repl_prime : char → char
| '\'' := '@'
| c := c

def to_smt_name : name → smt.name :=
string.map repl_prime ∘ name.to_string_with_sep "_"

inductive expr'
| all : smt.name → type → expr' → expr'
| exist : smt.name → type → expr' → expr'
| var : ℕ → expr'
| lit : ℕ → expr'
| const : smt.name → expr'
| app : smt.name → list expr' → expr'

open smt.expr'

mutual inductive bounded, all_bounded
with bounded : expr' → ℕ → Prop
| all {n t e b} :
  bounded e (b+1) →
  bounded (all n t e) b
| exist {n t e b} :
  bounded e (b+1) →
  bounded (exist n t e) b
| var {n b} : n < b → bounded (var n) b
| const {n b} : bounded (const n) b
| lit {n b} : bounded (lit n) b
| app {fn args b} :
  all_bounded args b →
  bounded (expr'.app fn args) b
with all_bounded : list expr' → ℕ → Prop
| nil {b} : all_bounded [] b
| cons {x xs b} :
  bounded x b →
  all_bounded xs b →
  all_bounded (x :: xs) b

def expr := { e // bounded e 0 }

meta def type.to_z3 : _root_.expr → string ⊕ type
| `(ℤ) := sum.inr type.int
| `(ℝ) := sum.inr type.real
| `(%%a → %%b) := type.array <$> type.to_z3 a <*> type.to_z3 b
| e := sum.inl $ (format!"type not supported: {e}").to_string

meta def z3_builtin : rbmap name (ℕ × name) :=
rbmap.from_list
[ (`eq, 1, `=),
  (`has_lt.lt, 1, `<),
  (`has_add.add, 2, `+),
  (`has_mul.mul, 2, `*),
  (`has_sub.sub, 2, `-),
  (`has_neg.neg, 2, `-),
  (`has_pow.pow, 3, `^),
  (`not, 0, `not) ]

meta def mk_lit : _root_.expr → string ⊕ ℕ
| `(bit0 %%e) := (*2) <$> mk_lit e
| `(bit1 %%e) := (λ n, 2*n + 1) <$> mk_lit e
| `(@has_zero.zero _ _) := pure 0
| `(@has_one.one _ _) := pure 1
| e := sum.inl (format!"invalid numeral {e}").to_string

meta def to_z3' : _root_.expr → string ⊕ expr'
| (expr.var n) := sum.inr $ expr'.var n
| (expr.const n t) := sum.inr $ expr'.const (to_smt_name n)
| e@`(bit0 _) := expr'.lit <$> mk_lit e
| e@`(bit1 _) := expr'.lit <$> mk_lit e
| e@`(@has_zero.zero _ _) := expr'.lit <$> mk_lit e
| e@`(@has_one.one _ _) := expr'.lit <$> mk_lit e
| e@(expr.app e₀ e₁) :=
let fn := e₀.get_app_fn,
    args := e.get_app_args in
if fn.is_constant then do
  match z3_builtin.find fn.const_name with
  | (some (i,n)) :=
  expr'.app (to_smt_name n) <$> (args.drop i).traverse to_z3'
  | none := sum.inl (format!"invalid function: {fn.const_name}").to_string
  end
else sum.inl "invalid function application"
| (expr.lam _ _ _ _) := sum.inl "lambdas are not supported"
| (expr.pi n _ d b) := all (to_smt_name n) <$> type.to_z3 d <*> to_z3' b
| (expr.elet n d t b) := sum.inl "let are not supported"
| (expr.local_const _ n _ _) := sum.inr $ const (to_smt_name n)
| (expr.mvar _ _ _) := sum.inl "mvars are not supported"
| (expr.sort _) := sum.inl "sort is not supported"
| (expr.macro _ _) := sum.inl "macros are not supported"

lemma bounded.of_all {n t e b} : bounded (all n t e) b → bounded e (b+1)
| (bounded.all h) := h

lemma bounded.of_exist {n t e b} : bounded (exist n t e) b → bounded e (b+1)
| (bounded.exist h) := h

lemma bounded.of_var {n b} : bounded (var n) b → n < b
| (bounded.var h) := h

lemma bounded.of_app {fn args b} : bounded (expr'.app fn args) b → all_bounded args b
| (bounded.app h) := h

lemma all_bounded.head {x xs b} : all_bounded (x :: xs) b → bounded x b
| (all_bounded.cons h _) := h

lemma all_bounded.tail {x xs b} : all_bounded (x :: xs) b → all_bounded xs b
| (all_bounded.cons _ h) := h

def decidable.map {p q : Prop} (f : p → q) (g : q → p) : decidable p → decidable q
| (is_true p) := is_true $ f p
| (is_false p) := is_false $ λ h, p (g h)

-- open tactic
-- meta def prove_dec : tactic unit :=
-- do try well_founded_tactics.default_dec_tac,
--    `[dsimp [has_well_founded.r,sizeof_measure,measure,inv_image,sizeof]],
--    `[dsimp [has_sizeof.sizeof,psum.sizeof,sizeof]],
--    `[dsimp [psigma.sizeof]],
--    -- constructor,
--    trace_state

mutual def bounded.decide, all_bounded.decide
with bounded.decide : Π e b, decidable (bounded e b)
| (var v) := λ b,
if h : v < b then is_true  $ bounded.var h
             else is_false $ by { intro, cases a, apply h a_a }
| (const n) := λ b, is_true $ bounded.const
| (lit n) := λ b, is_true $ bounded.lit
| (all n t e) := λ b,
  -- have sizeof e < sizeof n + (sizeof t + sizeof e), from _,
  decidable.map bounded.all bounded.of_all (bounded.decide e (b+1))
| (exist n t e) := λ b, decidable.map bounded.exist bounded.of_exist (bounded.decide e $ b+1)
| (app fn args) := λ b, decidable.map bounded.app bounded.of_app (all_bounded.decide args b)
with all_bounded.decide : Π es b, decidable (all_bounded es b)
| [] := λ b, is_true all_bounded.nil
| (e :: es) := λ b,
have 2 < 1 + (1 + (1 + list.sizeof es)), by linarith,
match bounded.decide e b with
| (is_true h) :=
  match all_bounded.decide es b with
  | (is_true h') := is_true (all_bounded.cons h h')
  | (is_false h') := is_false (λ h'', h' h''.tail)
  end
| (is_false h) := is_false (λ h', h h'.head)
end

local attribute [instance] bounded.decide all_bounded.decide

mutual def expr'.to_string_aux, expr'.to_string_aux'
with expr'.to_string_aux : Π (e : expr') (vs : list smt.name), bounded e vs.length → string
| (all v t e) vs h :=
  "(forall ((" ++ v ++ " " ++ t.to_string ++ ")) " ++ e.to_string_aux (v :: vs) h.of_all ++ ")"
| (exist v t e) vs h := "(exists ((" ++ v ++ " " ++ t.to_string ++ ")) " ++ e.to_string_aux (v :: vs) h.of_exist ++ ")"
| (var v) vs h := (vs.nth_le v h.of_var).to_string
| (const v) _ _ := v
| (lit v) _ _ := to_string v
| (app fn args) vs h := "(" ++ fn ++ expr'.to_string_aux' args vs h.of_app ++ ")"
with expr'.to_string_aux' : Π (e : list expr') (vs : list smt.name), all_bounded e vs.length → string
| [] vs _ := ""
| (x :: xs) vs h :=
have 2 < 1 + (1 + (1 + list.sizeof xs)), by linarith,
" " ++ x.to_string_aux vs h.head ++ expr'.to_string_aux' xs vs h.tail

def expr.to_string : expr → string
| ⟨e,h⟩ := e.to_string_aux [] h

meta def to_z3 (e : _root_.expr) : string ⊕ expr :=
do e' ← to_z3' e,
   if h : bounded e' 0 then pure ⟨e',h⟩
                       else sum.inl "wrong use of bound variables"

meta def encode_local (v : _root_.expr) : tactic string :=
do t ← tactic.infer_type v,
   p ← tactic.is_prop t,
   if p then do
     e' ← to_z3 t,
     -- pure (format!"(assert (! {e'.to_string} :named {v.local_pp_name}))\n").to_string
     pure (format!"(assert {e'.to_string})\n").to_string
   else do
     t ← type.to_z3 t,
     -- pure (format!"(declare-const {v.local_pp_name} {t.to_string})\n").to_string
     pure (format!"(declare-fun {(to_smt_name v.local_pp_name).to_string} () {t.to_string})\n").to_string

end smt

namespace smt.parser
open smt (atom sexpr)
open smt.atom

def white := () <$ sat char.is_whitespace

def space := () <$ many white
def space1 := () <$ many1 white

def ident := (mk_simple_name ∘ list.as_string) <$> parser.many1 (sat char.is_alphanum <|> '_' <$ ch '_')

def is_printable (c : char) : Prop :=
32 ≤ c.val ∧ c.val ≤ 126

def is_symbol (c : char) : Prop :=
c ∈ ("~!@$%^&*_-+=<>.?/").to_list

instance is_printable.decidable_pred : decidable_pred is_printable :=
λ c, (by apply_instance : decidable (32 ≤ c.val ∧ c.val ≤ 126))

instance is_symbol.decidable_pred : decidable_pred is_symbol :=
λ c, (by apply_instance : decidable (c ∈ ("~!@$%^&*_-+=<>.?/").to_list))

def simple_symbol : parser string := list.as_string <$> parser.many1 (sat is_symbol <|> sat char.is_alphanum)
def symbol : parser atom := sym <$> simple_symbol
-- def keyword : parser atom := ch ':' *> atom.keyword <$> simple_symbol

def nat.of_char : list char → ℕ :=
list.foldl (λ n c, 10 * n + c.val - '0'.val) 0

def nat.bin_of_char : list char → ℕ :=
list.foldl (λ n c, 2 * n + c.val - '0'.val) 0

def nat.hex_of_char : list char → ℕ :=
let digit := "0123456789abcdef".to_list in
list.foldl (λ n c, 16 * n + list.index_of c.to_lower digit) 0

def rat.of_char : list char → ℚ :=
list.foldl (λ n (c : char), (n + ↑(c.val - '0'.val)) / 10) 0 ∘ list.reverse

def non_zero : parser char :=
sat $ λ d, char.is_digit d ∧ d ≠ '0'

def numerals : parser (list char) :=
((::) <$> non_zero <*> many (sat char.is_digit)) <|>
['0'] <$ ch '0'

def parse_nat : parser ℕ :=
nat.of_char <$> numerals

def decimal : parser atom :=
do x ← numerals,
   do { ch '.', many (ch '0'),
        y ← numerals,
        pure $ dec $ nat.of_char x + rat.of_char y } <|>
     pure (num $ nat.of_char x)

def any_of (xs : list char) : parser char :=
sat (∈ xs)

def hexa : parser atom :=
str "#x" *>
(num ∘ coe ∘ nat.hex_of_char) <$> many1 (sat char.is_digit <|> any_of "abcdefABCDEF".to_list)

def bin : parser atom :=
str "#b" *>
(num ∘ coe ∘ nat.bin_of_char) <$> many1 (any_of ['0','1'])

-- def parse_string : parser atom :=
-- ch '\"' *>
-- (atom.str ∘ list.as_string) <$> many
--           ('\"' <$ str "\"\"" <|>
--             sat (λ c, is_printable c ∧ c ≠ '\"') <|>
--             sat char.is_whitespace) <*
-- ch '\"'

def parse_atom : parser atom :=
decimal <|> hexa <|> bin <|>
-- parse_string <|>
symbol -- <|> keyword

def sexpr_parser : parser sexpr :=
parser.fix $ λ parser, (smt.sexpr.const <$> parse_atom) <|> (smt.sexpr.fapp <$> (ch '(' *> sep_by space parser <* ch ')') )

def brackets {α} (l r : string) (p : parser α) : parser α :=
str l *> p <* str r

def base_name : name → string
| (name.mk_string s _) := s
| _ := ""

open smt.sexpr tactic

meta def mk_assoc (n : name) : list expr → tactic expr
| [] := fail "mk_assoc []"
-- | [x] := pure x
| (x :: xs) :=
  do mfoldl (λ a b, mk_app n [a,b]) x xs

meta def expr.of_sexpr : sexpr → tactic expr
| (const (num n)) := pure `(n : _)
| (const (dec n)) := pure `(n)
-- | (const (sym "=")) := to_expr ``(@eq _)
-- | (const (sym "-")) := to_expr ``(@has_sub.sub _ _)
-- | (const (sym "+")) := to_expr ``(@has_add.add _ _)
| (const (sym s)) := resolve_name s >>= to_expr
| (fapp (const (sym "-") :: [x,y]))  := [x,y].mmap expr.of_sexpr >>= mk_app ``has_sub.sub
| (fapp (const (sym "-") :: [x]))    := [x].mmap expr.of_sexpr >>= mk_app ``has_neg.neg
| (fapp (const (sym "not") :: [x]))  := [x].mmap expr.of_sexpr >>= mk_app ``not
| (fapp (const (sym "+") :: xs))     := xs.mmap expr.of_sexpr >>= mk_assoc ``has_add.add
| (fapp (const (sym "and") :: xs))   := xs.mmap expr.of_sexpr >>= mk_assoc ``_root_.and
| (fapp (const (sym "=") :: [x,y]))  := [x,y].mmap expr.of_sexpr >>= mk_app ``eq
| (fapp (const (sym "<=") :: [x,y])) := [x,y].mmap expr.of_sexpr >>= mk_app ``has_le.le
| (fapp (const (sym "<") :: [x,y])) := [x,y].mmap expr.of_sexpr >>= mk_app ``has_lt.lt
| e@(fapp _) := fail format!"fapp {e.to_string}"


meta def and_prj : ℕ → expr → expr → tactic expr
| 0 `(%%p ∧ %%q) h :=
     mk_mapp ``and.elim_left [p,q,h]
| 0 p h := mk_app ``id [h]
| (i+1) `(%%p ∧ %%q) h :=
  mk_mapp ``and.elim_right [p,q,h] >>= and_prj i q
| (i+1) p h := fail format!"invalid conjunction {p}"

meta def clear_except (ls : list expr) : tactic unit :=
do n  ← revert_lst ls,
   hs ← local_context,
   hs.reverse.mmap $ λ h, try $ clear_lst [h.local_pp_name],
   intron n

end smt.parser

namespace smt

meta structure solver :=
( cmd : string )
( args : list string )
( options : list string := [] )
( output_to_file : option string := none )
( proof_type : Type )
( read : parser proof_type )
( execute : proof_type → tactic unit )

meta instance : hashable solver :=
{ hash_with_salt := λ ⟨a,b,c,d,_,_,_⟩, hash_with_salt (a,b,c,d) }

@[derive [has_repr,hashable]]
inductive logic_fragment
| AUFLIA | AUFLIRA | LIA | LRA
| QF_AUFLIA | QF_AX | QF_IDL | QF_LIA
| QF_LRA | QF_RDL | QF_UF
| QF_UFIDL | QF_UFLIA | QF_UFLRA | UFLRA
| QF_NIA | QF_NRA
-- |QF_UF
-- |QF_IDL
-- |QF_RDL
-- |QF_UFIDL

end smt
