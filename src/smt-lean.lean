
import tactic
import tactic.linarith
import system.io

open io io.fs io.process parser

def sum.coe {m α} [monad m] [monad_fail m] : string ⊕ α → m α
| (sum.inl e) := monad_fail.fail $ "\n" ++ e
| (sum.inr e) := pure e

meta instance {α} : has_coe (string ⊕ α) (tactic α) := ⟨ sum.coe ⟩
instance sum.io_coe {α} : has_coe (string ⊕ α) (io α) := ⟨ sum.coe ⟩

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
| int | array (idx rng : type)

open smt.type

def type.to_string : type → string
| int := "Int"
| (array t₀ t₁) := "(Array " ++ t₀.to_string ++ " " ++ t₁.to_string ++ ")"

inductive expr'
| all : name → type → expr' → expr'
| exist : name → type → expr' → expr'
| var : ℕ → expr'
| lit : ℕ → expr'
| const : name → expr'
| app : name → list expr' → expr'

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
| `(%%a → %%b) := type.array <$> type.to_z3 a <*> type.to_z3 b
| e := sum.inl $ (format!"type not supported: {e}").to_string

meta def z3_builtin : rbmap name (ℕ × name) :=
rbmap.from_list
[ (`eq, 1, `=),
  (`has_add.add, 2, `+),
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
| (expr.const n t) := sum.inr $ expr'.const n
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
  expr'.app n <$> (args.drop i).traverse to_z3'
  | none := sum.inl (format!"invalid function: {fn.const_name}").to_string
  end
else sum.inl "invalid function application"
| (expr.lam _ _ _ _) := sum.inl "lambdas are not supported"
| (expr.pi n _ d b) := all n <$> type.to_z3 d <*> to_z3' b
| (expr.elet n d t b) := sum.inl "let are not supported"
| (expr.local_const _ n _ _) := sum.inr $ const n
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
with expr'.to_string_aux : Π (e : expr') (vs : list name), bounded e vs.length → string
| (all v t e) vs h :=
  "(forall ((" ++ v.to_string ++ " " ++ t.to_string ++ ")) " ++ e.to_string_aux (v :: vs) h.of_all ++ ")"
| (exist v t e) vs h := "(exists ((" ++ v.to_string ++ " " ++ t.to_string ++ ")) " ++ e.to_string_aux (v :: vs) h.of_exist ++ ")"
| (var v) vs h := (vs.nth_le v h.of_var).to_string
| (const v) _ _ := v.to_string
| (lit v) _ _ := to_string v
| (app fn args) vs h := "(" ++ fn.to_string ++ expr'.to_string_aux' args vs h.of_app ++ ")"
with expr'.to_string_aux' : Π (e : list expr') (vs : list name), all_bounded e vs.length → string
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
     pure (format!"(declare-fun {v.local_pp_name} () {t.to_string})\n").to_string

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

inductive proof_step
| input (s : sexpr)
| tmp_LA_pre (s : sexpr) (r : ℕ)
--  * deep_res          : deep resolution in formula
--  * true              : valid: {true}
--  * false             : valid: {(not false)}
--  * and_pos           : valid: {(not (and a_1 ... a_n)) a_i}
--  * and_neg           : valid: {(and a_1 ... a_n) (not a_1) ... (not a_n)}
--  * or_pos            : valid: {(not (or a_1 ... a_n)) a_1 ... a_n}
--  * or_neg            : valid: {(or a_1 ... a_n) (not a_i)}
--  * xor_pos1          : valid: {(not (xor a b)) a b}
--  * xor_pos2          : valid: {(not (xor a b)) (not a) (not b)}
--  * xor_neg1          : valid: {(xor a b) a (not b)}
--  * xor_neg2          : valid: {(xor a b) (not a) b}
--  * implies_pos       : valid: {(not (implies a b)) (not a) b}
--  * implies_neg1      : valid: {(implies a b) a}
--  * implies_neg2      : valid: {(implies a b) (not b)}
--  * equiv_pos1        : valid: {(not (iff a b)) a (not b)}
--  * equiv_pos2        : valid: {(not (iff a b)) (not a) b}
--  * equiv_neg1        : valid: {(iff a b) (not a) (not b)}
--  * equiv_neg2        : valid: {(iff a b) a b}
--  * ite_pos1          : valid: {(not (if_then_else a b c)) a c}
--  * ite_pos2          : valid: {(not (if_then_else a b c)) (not a) b}
--  * ite_neg1          : valid: {(if_then_else a b c) a (not c)}
--  * ite_neg2          : valid: {(if_then_else a b c) (not a) (not b)}
--  * eq_reflexive      : valid: {(= x x)}
--  * eq_transitive     : valid: {(not (= x_1 x_2)) ... (not (= x_{n-1} x_n)) (= x_1 x_n)}
--  * eq_congruent      : valid: {(not (= x_1 y_1)) ... (not (= x_n y_n)) (= (f x_1 ... x_n) (f y_1 ... y_n))}
--  * eq_congruent_pred : valid: {(not (= x_1 y_1)) ... (not (= x_n y_n)) (not (p x_1 ... x_n)) (p y_1 ... y_n)}
--  * eq_congruent_general : valid: {(not (= x_1 y_1)) ... (not (= x_n y_n)) (not (p t_1 ... x_1 ... t_m ... x_n)) (p t_1 ... y_1 ... t_m ... y_n)}
--  * distinct_elim     : valid: {(= DIST(...) ... neq ...)}
--  * chainable_elim    : valid: {(= (f t1 ... tn ) (and (f t1 t2 ) (f t2 t3 ) ... (f tn−1 tn ))}
--  * right_assoc_elim  : valid: {(= (f t1 ... tn ) (f t1 (f t2 ... (f tn−1 tn ) ... )}
--  * left_assoc_elim   : valid: {(= (f t1 ... tn ) (f ... (f (f t1 t2 ) t3 ) ... tn )}
--  * la_rw_eq          : valid: {(= (a = b) (and (a <= b) (b <= a))}
--  * la_generic        : valid: not yet defined
--  * lia_generic       : valid: not yet defined
--  * nla_generic       : valid: not yet defined
--  * la_disequality    : valid: not yet defined
--  * la_totality       : valid: {(le t1 t2), (le t2 t1)}
| la_tautology (e : sexpr)
--  * la_tautology      : valid: linear arithmetic tautology without variable
--  * forall_inst       : valid: {(implies (forall X (A X)) (A {X \ t}))}
--  * exists_inst       : valid: {(implies (A t) (exists X (A {t \ X})))}
--  * skolem_ex_ax      : valid: {(not (exists X (A X))), A(sk)} where sk is fresh
--  * skolem_all_ax     : valid: {(not A(sk)), (forall X (A X))} where sk is fresh
--  * qnt_simplify_ax   : valid: to be defined
--  * qnt_merge_ax      : valid: {(not (Q x (Q y (F x y)))), (Q x y (F x y)))} where sk is fresh
--  * fol_ax            : valid: to be defined [produced by the E prover]
--  * th_resolution     : resolution of 2 or more clauses from theory reasoner
| resolution (_ : unit) (_ : list ℕ)
--  * resolution        : resolution of 2 or more clauses from SAT solver
| and (e : sexpr) (r : ℕ) (n : ℕ)
--  * and               : {(and a_1 ... a_n)} --> {a_i}
--  * not_or            : {(not (or a_1 ... a_n))} --> {(not a_i)}
--  * or                : {(or a_1 ... a_n)} --> {a_1 ... a_n}
--  * not_and           : {(not (and a_1 ... a_n))} --> {(not a_1) ... (not a_n)}
--  * xor1              : {(xor a b)} --> {a b}
--  * xor2              : {(xor a b)} --> {(not a) (not b)}
--  * not_xor1          : {(not (xor a b))} --> {a (not b)}
--  * not_xor2          : {(not (xor a b))} --> {(not a) b}
--  * implies           : {(implies a b)} --> {(not a) b}
--  * not_implies1      : {(not (implies a b))} --> {a}
--  * not_implies2      : {(not (implies a b))} --> {(not b)}
--  * equiv1            : {(iff a b)} --> {(not a) b}
--  * equiv2            : {(iff a b)} --> {a (not b)}
--  * not_equiv1        : {(not (iff a b))} --> {a b}
--  * not_equiv2        : {(not (iff a b))} --> {(not a) (not b)}
--  * ite1              : {(if_then_else a b c)} --> {a c}
--  * ite2              : {(if_then_else a b c)} --> {(not a) b}
--  * not_ite1          : {(not (if_then_else a b c))} --> {a (not c)}
--  * not_ite2          : {(not (if_then_else a b c))} --> {(not a) (not b)}
--  * tmp_alphaconv     : {formula} --> {alpha conversion with fresh symbols}
--  * tmp_let_elim      : {formula} --> {formula where let have been eliminated}
--  * tmp_nary_elim     : {formula} --> {formula where n-ary symbols have been eliminated}
--  * tmp_distinct_elim : {formula} --> {formula where distinct have been eliminated}
--  * tmp_eq_norm       : {formula} --> {formula where eqs between propositions have been turned into equivs}
--  * tmp_simp_arith    : {formula} --> {formula where arith terms have been normalized}
--  * tmp_ite_elim      : {formula} --> {formula where ite terms have been eliminated}
--  * tmp_macrosubst    : {formula} --> {formula where macros have been substituted}
--  * tmp_betared       : {formula} --> {formula where beta reduction has been applied}
--  * tmp_bfun_elim     : {formula} --> {formula where functions with Boolean arguments have been simplified}
--  * tmp_sk_connector  : {formula} --> {formula where some connectors have been suppressed for skolemization}
--  * tmp_pm_process    : {formula} --> {formula where polymorphism has been eliminated}
--  * tmp_qnt_tidy      : {formula} --> {formula where quantifiers have been normalized}
--  * tmp_qnt_simplify  : {formula} --> {formula where quantifiers have been simplified}
--  * tmp_skolemize     : {formula} --> {Skolemized formula}
--  * subproof          :
-- The following deduction types require exactly one clause_id argument:
--  * and
--  * not_or
--  * or
--  * not_and
--  * xor1
--  * xor2
--  * not_xor1
--  * not_xor2
--  * implies
--  * not_implies1
--  * not_implies2
--  * equiv1
--  * equiv2
--  * not_equiv1
--  * not_equiv2
--  * ite1
--  * ite2
--  * not_ite1
--  * not_ite2
--  * tmp_alphaconv
--  * tmp_let_elim
--  * tmp_nary_elim
--  * tmp_distinct_elim
--  * tmp_eq_norm
--  * tmp_simp_arith
--  * tmp_ite_elim
--  * tmp_macrosubst
--  * tmp_betared
--  * tmp_bfun_elim
--  * tmp_sk_connector
--  * tmp_pm_process
--  * tmp_qnt_tidy
--  * tmp_qnt_simplify
--  * tmp_skolemize
--  * subproof
-- The following deduction types may have any number of clause_id arguments:
--  * deep_res
--  * th_resolution
--  * resolution
-- The following deduction types require exactly one integer parameter:
--  * and_pos
--  * or_neg
--  * and
--  * not_or


def proof := list (ℕ × proof_step)

-- #eval nat.of_char ['1','2','3','0']

def brackets {α} (l r : string) (p : parser α) : parser α :=
str l *> p <* str r

def base_name : name → string
| (name.mk_string s _) := s
| _ := ""

section
open tactic

meta def mk_field_parser : expr → tactic expr
| `(sexpr) := to_expr ``( brackets "(" ")" sexpr_parser <* space )
| `(list sexpr) := to_expr ``( brackets "(" ")" (sep_by space sexpr_parser) <* space )
| `(ℕ) := to_expr ``(parse_nat <* space)
| `(unit) := to_expr ``(brackets "(" ")" space <* space)
| `(list ℕ) := to_expr ``( many (parse_nat <* space) )
| e := fail format!"invalid field type {e}"

meta def mk_choice : list expr → tactic expr
| [] := fail "empty list"
| [p] := pure p
| (p :: ps) :=
  do x ← mk_choice ps,
     mk_app ``has_orelse.orelse [p,x]

-- set_option trace.app_builder true
def read_proof_step : parser proof_step :=
by do {
   e ← tactic.get_env,
   let cs := e.constructors_of ``proof_step,
   ps ← cs.mmap $ λ c,
     do { let c' := base_name c,
          c ← mk_const c,
          (t,_) ← infer_type c >>= mk_local_pis,
          t ← t.mmap infer_type,
          e ← to_expr ``(pure %%c : parser _),
          e ←  mfoldl (λ x y, do
            y ← mk_field_parser y,
            mk_app ``has_seq.seq [x,y]) e t,
          to_expr ``(str %%(reflect c') *> space *> %%e) },
   e ← mk_choice ps,
   -- trace e,
   exact e }

end
-- (str "input" *> space *> proof_step.input <$> brackets "(" ")" sexpr_parser) <|>
-- (str "tmp_LA_pre" *> space *> proof_step.tmp_LA_pre <$> brackets "(" ")" (sep_by space sexpr_parser) <* space <*> parse_nat) <|>
                                                       -- (brackets "(" ")" (sep_by space sexpr_parser) <* space)
-- (str "and" *> space *> proof_step.and <$> brackets "(" ")" (sexpr_parser) <* space <*> parse_nat <* space <*> parse_nat)

def read_proof : parser proof :=
many (prod.mk <$> parse_nat <* ch ':' <*> brackets "(" ")" read_proof_step <* space)

end smt.parser

namespace smt

open parser tactic ( unsafe_run_io )

def parse_log (fn : string) :=
do p ← io.fs.read_file fn,
   parser.run (parser.read_proof) p

-- def foo_bar :=
-- do h ← io.proc.spawn
--         { cmd := "veriT",
--           args := [
--                    -- "--proof-prune","--proof-merge","--proof-with-sharing",
--                            -- "--cnf-definitional","--disable-ackermann",
--                            -- "--disable-e",
--                            -- "--max-time=3",
--                            -- "--input=smtlib2",
--                            -- "--print-flat",
--                            -- "--disable-banner",
--                            -- "--print-simp-and-exit",
--                            "--proof=file.log"
--                              -- "--input=test.smt",
--                              -- "test.smt"
--                            ],
--           stdin := stdio.piped,
--           stdout := stdio.piped,
--           stderr := stdio.piped,
--           -- cwd := _,
--           -- env := _
--           },
--    -- xs ← buffer.to_string <$> io.fs.read_file "test.smt",
--    -- io.fs.put_str_ln h.stdin xs,
--    let xs := [ "; Integer arithmetic",
--                "(set-option :print-success false)",
--                "(set-option :produce-proofs true)",
--                "(set-logic QF_LIA)",
--                ";; (echo \"foo\")",
--                "(declare-fun x ( ) Int)",
--                "(declare-fun y ( ) Int)",
--                "(assert (! (= (- x y) (+ x (- y) 1)) :named h0))",
--                "(assert (= x y))",
--                "(check-sat)",
--                ";; (get-value ((x 0) (y 0) (x 1) (y 1)))",
--                ";; (get-model)",
--                "(get-proof)",
--                "; unsat",
--                ";; (exit)" ],
--    xs.mmap' (io.fs.put_str_ln h.stdin),
--    io.fs.close h.stdin,
--    -- dir ← io.env.get_cwd,
--    -- io.print $ dir.to_list,
--    -- io.put_str_ln h,
--    -- h' ← io.cmd { cmd := "pwd" },
--    -- io.put_str_ln h',
--    io.put_str_ln "stderr",
--    xs ← read_to_end h.stderr,
--    io.put_str_ln xs.to_string,
--    io.put_str_ln "stdout",
--    xs ← read_to_end h.stdout,
--    io.put_str_ln xs.to_string,
--    io.proc.wait h,
--    parse_log,
--    pure ()

-- run_cmd unsafe_run_io parse_log -- unsafe_run_io foo_bar

end smt

-- meta instance name.reflect : has_reflect name
-- | name.anonymous        := `(name.anonymous)
-- | (name.mk_string  s n) := `(λ n, name.mk_string  s n).subst (name.reflect n)
-- | (name.mk_numeral i n) := `(λ n, name.mk_numeral i n).subst (name.reflect n)

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

namespace tactic.interactive

open smt (hiding expr) tactic smt.parser smt.parser.proof_step
open smt.sexpr smt.atom

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
| e@(fapp _) := fail format!"fapp {e.to_string}"


meta def and_prj : ℕ → expr → expr → tactic expr
| 0 `(%%p ∧ %%q) h :=
     mk_mapp ``and.elim_left [p,q,h]
| 0 p h := mk_app ``id [h]
| (i+1) `(%%p ∧ %%q) h :=
  mk_mapp ``and.elim_right [p,q,h] >>= and_prj i q
| (i+1) p h := fail format!"invalid conjunction {p}"

meta def clear_except (ls : list expr) : tactic unit :=
do -- ls ← ls.mmap get_local,
   n  ← revert_lst ls,
   hs ← local_context,
   hs.reverse.mmap $ λ h, try $ clear_lst [h.local_pp_name],
   intron n

open native ( rb_map )
meta def run_step (m : rb_map ℕ expr) : ℕ × proof_step → tactic (rb_map ℕ expr)
| (i, input x) := do
  x ← expr.of_sexpr x,
  h ← assert `h x,
  assumption,
  pure $ m.insert i h
| (i, tmp_LA_pre e j) := do
  e' ← expr.of_sexpr e,
  h ← m.find j,
  pr ← to_expr ``(le_antisymm_iff.mp %%h),
  h ← note `h' (some e') pr,
  pure $ m.insert i h
| (i, and e j k) := do
  e' ← expr.of_sexpr e,
  h ← m.find j,
  e'' ← infer_type h,
  p ← and_prj k e'' h,
  h ← note `h (some e') p,
  pure $ m.insert i h
| (i, la_tautology e) := do
  e' ← expr.of_sexpr e,
  h ← assert `h e',
  clear_except [],
  linarith [] none,
  pure $ m.insert i h
| (i, resolution _ rs) := do
  hs ← rs.mmap $ λ h, m.find h,
  clear_except hs,
  tautology,
  pure m
-- | _ := fail "run_step"

meta def write_formulas (xs : list string) (h : handle) : io unit :=
do let opts := [
               "(set-option :print-success false)",
               "(set-option :produce-proofs true)",
               "(set-logic QF_LIA)" ],
   opts.mmap' $ io.fs.put_str_ln h,
   xs.mmap' $ io.fs.put_str h,
   io.fs.put_str_ln h "(check-sat)",
   io.fs.put_str_ln h "(get-proof)"

@[user_attribute]
meta def proof_file_names : user_attribute unit (list $ string × ℕ) :=
{ name := `proof_file_names,
  descr := "central table of proof file names",
  parser := pure [] }

@[proof_file_names]
def proof_files := unit

meta def unique_file_name (ext : string) : tactic string :=
do ls ← native.rb_map.of_list <$>  proof_file_names.get_param ``proof_files,
   n ← decl_name,
   let fn := n.to_string_with_sep "_",
   i ← ls.find fn <|> pure 0,
   let ls' := ls.insert fn (i+1),
   proof_file_names.set ``proof_files ls'.to_list tt,
   pure $ fn ++ "_" ++ to_string i ++ "." ++ ext

meta def call_solver (fn : string) (xs : list string) : tactic string :=
unsafe_run_io $
do -- h ← mk_file_handle "text.smt" io.mode.write ff,
   -- close h,
   h ← io.proc.spawn
     -- { cmd := "z3",
     --   args := ["-in","-smt2"],
     --   stdin := stdio.piped,
     --   stdout := stdio.piped,
     --   stderr := stdio.piped },
     { cmd := "veriT",
       args := ["--proof="++fn,"--max-time=5","--input=smtlib2","--disable-banner"],
       stdin := stdio.piped,
       stdout := stdio.piped,
       stderr := stdio.piped },
   write_formulas xs h.stdin,
   close h.stdin,
   -- xs ← buffer.to_string <$> read_to_end h.stdout,
   -- io.put_str_ln xs,
   -- xs ← buffer.to_string <$> read_to_end h.stderr,
   -- io.put_str_ln xs,
   proc.wait h,
   pure fn

meta def veriT : tactic unit :=
do by_contradiction none,
   dedup,
   fn ← unique_file_name "log",
   ls ← local_context,
   ps ← ls.mmap encode_local,
   fn ← call_solver fn ps,
   p ← tactic.unsafe_run_io $ parse_log fn,
   mfoldl run_step (native.rb_map.mk _ _) p,
   pure ()

end tactic.interactive
-- set_option trace.app_builder true


example {x y : ℤ} (h1 : ((x - y) = (x + (- y) + 1)))
 : x = x :=
begin
  veriT,
end

example {x y : ℤ} (h1 : ((x - y) = (x + (- y) + 2)))
 : x = x :=
begin
  veriT,
end

-- section some_algorithm

-- variables n x n' x' : ℤ
-- variables Act₀ : n' = n + 1
-- variables J₀ : x = n^3

-- example : x' = n'^3 :=
-- by veriT

-- end some_algorithm

-- example {α : Type} {x y z : α}
--   (h : x = y) (h' : y = z)
--  : x = z :=
-- begin
--   veriT,
-- end

-- example {α : Type} {z : α} {x y : list α}
--   (h : (z :: x : list α) = z :: y)
--  : x = y :=
-- begin
--   veriT,
-- end
