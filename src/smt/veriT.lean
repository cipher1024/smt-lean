
import tactic.linarith
import smt.basic

namespace smt.veriT
open smt (hiding expr)

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

namespace parser

open tactic smt.parser parser

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

-- (str "input" *> space *> proof_step.input <$> brackets "(" ")" sexpr_parser) <|>
-- (str "tmp_LA_pre" *> space *> proof_step.tmp_LA_pre <$> brackets "(" ")" (sep_by space sexpr_parser) <* space <*> parse_nat) <|>
                                                       -- (brackets "(" ")" (sep_by space sexpr_parser) <* space)
-- (str "and" *> space *> proof_step.and <$> brackets "(" ")" (sexpr_parser) <* space <*> parse_nat <* space <*> parse_nat)

def read_proof : parser proof :=
many (prod.mk <$> parse_nat <* ch ':' <*> brackets "(" ")" read_proof_step <* space)

end parser

open native ( rb_map ) proof_step tactic smt.parser tactic.interactive (linarith)

meta def run_step (m : rb_map ℕ expr) : ℕ × proof_step → tactic (rb_map ℕ expr)
| (i, input x) := do
  trace x.to_string,
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
  tautology tt,
  pure m

end smt.veriT

namespace smt

open veriT

meta def veriT : solver :=
{ cmd := "veriT",
  args := ["--proof-merge","--proof-prune",
           "--input=smtlib2","--disable-banner"],
  options := [ "(set-option :print-success false)",
               "(set-option :dot_proof_file proof.dot)" ],
  output_to_file := some "--proof=",
  proof_type := proof,
  read := parser.read_proof,
  execute := λ p, () <$ mfoldl run_step (native.rb_map.mk _ _) p }

end smt
