import tactic.finish tactic.tidy

open expr
namespace tactic

section intro_ext

meta def intro_ext_tactics : list (tactic string) :=
[ tactic.reflexivity                                 >> pure "refl",
  -- `[exact dec_trivial]                        >> pure "exact dec_trivial",
  -- propositional_goal >> assumption            >> pure "assumption",
  tidy.ext1_wrapper,
  intros1                                     >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  -- auto_cases,
  -- `[apply_auto_param]                         >> pure "apply_auto_param",
  -- `[dsimp at *]                               >> pure "dsimp at *",
  -- `[simp at *]                                >> pure "simp at *",
  -- fsplit                                      >> pure "fsplit",
  -- injections_and_clear                        >> pure "injections_and_clear",
  -- propositional_goal >> (`[solve_by_elim])    >> pure "solve_by_elim",
  -- `[unfold_aux]                               >> pure "unfold_aux",
  tidy.run_tactics ]

meta def intro_ext_cfg : tidy.cfg := {tactics := intro_ext_tactics}

-- example : (λ x : ℕ, x + 1) = λ x, 0 + x + 0 + 1  :=
-- begin
--  tidy? intro_ext_cfg,
-- end

end intro_ext

section lambda_lifting

/-- Given an expr f of the form λ x, body and an expr e, return the expr
    ∀ x, e x = body -/
protected meta def axiom_of_lambda (e : expr) : expr → tactic expr
  | (lam a b c d) := (let e_c := (app e (var 0)) in tactic.to_expr ``(%%e_c = %%d)) >>= λ x, return $ pi a b c x
  | (var n) := return $ var n
  | (sort l) := return $ sort l
  | (const a b) := return $ const a b
  | (mvar a b c) := return $ mvar a b c
  | (local_const a b c d) := return $ local_const a b c d
  | (app a b) := return $ app a b
  | (pi a b c d) := return $ pi a b c d
  | (elet a b c d) := return $ elet a b c d
  | (macro a b) := return $ macro a b

meta def trace_goal_raw : tactic unit :=
  target >>= tactic.trace ∘ to_raw_fmt

protected meta def lambda_set_core (a h : name) (v : expr) : tactic unit :=
do -- tp <- infer_type v,
   nv ← pose a none v,
   e <- (tactic.axiom_of_lambda nv v),
   trace e,
   axm ← (tactic.axiom_of_lambda nv v) >>= assert h,
   (intros >> tactic.interactive.refl) >> tactic.trace "intro + refl succeeded" <|> tactic.fail "intro + refl failed",
   pf ← to_expr ``(%%v = %%nv) >>= assert (h.append "_rw"),
   reflexivity,
     rw ← return pf,
     -- trace pf,
     s ← simp_lemmas.mk.add rw,
     -- trace "ajshdkh",
     h::hs ← list.filter (λ e, e ≠ pf) <$> non_dep_prop_hyps,
     -- trace "RAMALAMADINGDONG",
     tgt <- target,
     -- trace tgt,
     -- trace h,
     -- tactic.dsimp_target s []
     -- hyps.mmap (λ h, simp_hyp s [] h),
     trace "simp_hyp succeeded",
     tactic.try $ interactive.simp_core_aux {} (tactic.failed) s [] [h] tt,
     tgt <- (target >>= pp),
     trace ("target after simp call is now... \n ⊢ " ++ (to_string (tgt)))

meta def lambda_set : expr → tactic unit
  | (var n) := return ()
  | (sort l) := return ()
  | (const a b) := return ()
  | (mvar a b c) := lambda_set c
  | (local_const a b c d) := lambda_set d 
  | (app a b) := lambda_set a >> lambda_set b
  | (lam a b c d) := tidy intro_ext_cfg >> -- trace_goal_raw >> trace "tidy was called" >>
  (target >>= lambda_set) <|> tidy intro_ext_cfg <|>
                    fail_if_no_goals >>
                    -- trace_goal_raw >>
                    do n <- (tactic.get_unused_name "HEWWO"),
                        n' <- (tactic.get_unused_name "HERRO"),
                        tactic.trace "lambda_set_core is being called again",
                        tactic.lambda_set_core n n' (lam a b c d)
  | (pi a b c d) := -- tidy intro_ext_cfg >> trace "tidy was called'" >>  target >>= lambda_set <|> fail_if_no_goals
                    -- >>  
                    lambda_set c >> lambda_set d
  -- (tactic.get_unused_name) >>= tactic.intro >>= lambda_set
                     -- do n <- (tactic.get_unused_name),
                     --    n' <- (tactic.get_unused_name "HEWWO"),
                     --    tactic.trace "HELP!",
                     --    tactic.lambda_set n n' (pi a b c d)
  | (elet a b c d) := lambda_set b >> lambda_set c >> lambda_set d
  | (macro a b) := b.mfoldl (λ _ e, lambda_set e) ()

meta def trace_intro : tactic unit :=
  do e <- (tactic.get_unused_name "H") >>= tactic.intro,
  tactic.trace e.to_raw_fmt

meta def lambda_set_tactic : tactic unit := target >>= lambda_set

-- tidy intro_ext_cfg >> (target >>= lambda_set)
example : (λ x : ℕ, x + 1) = λ x, 0 + x + 0 + 1  :=
begin
  lambda_set_tactic, simp

/- tactic state is now
  HEWWO : ℕ → ℕ := λ (x : ℕ), x + 1,
  HERRO : ∀ (x : ℕ), HEWWO x = x + 1,
  HERRO._rw : (λ (x : ℕ), x + 1) = HEWWO,
  HEWWO_1 : ℕ → ℕ := λ (x : ℕ), 0 + x + 0 + 1,
  HERRO_1 : ∀ (x : ℕ), HEWWO_1 x = 0 + x + 0 + 1,
  HERRO_1._rw : (λ (x : ℕ), 0 + x + 0 + 1) = HEWWO_1
  ⊢ HEWWO = HEWWO_1
-/
end

/-
Note: the call to the simplifier annoyingly simplifies other parts of the target along with the intended rewrite. Possible fix: using rw instead of simp? Or use expr.replace and then change?

Also todo: hook this up to a fragment of tidy or chain, to keep trying to apply extensionality lemmas. The example above is vacuous because we can get rid of the lambdas with funext. After `chain` is finished, use `expr.is_sort` to check if there are any quantifications over sorts

In case we have assumptions with universal quantifications over types, we should also populate a list with all types which occur in the initial goal, plus types relevant to the target logic, with which to instantiate such quantifications
-/

end lambda_lifting

section is_first_order

/- Checks if an an expr contains a quantification over types -/
meta def contains_type_variables : expr → bool
  | (lam a b c d) := is_sort c ∨ contains_type_variables d
  | (var n) := ff
  | (sort l) := ff
  | (const a b) := ff
  | (mvar a b c) := contains_type_variables c
  | (local_const a b c d) := contains_type_variables d
  | (app a b) := contains_type_variables a ∨ contains_type_variables b
  | (pi a b c d) := is_sort c ∨ contains_type_variables d
  | (elet a b c d) := is_sort c ∨ contains_type_variables b ∨ contains_type_variables d
  | (macro a b) := (b.map contains_type_variables).foldr (λ x y, x ∨ y) ff

meta def contains_lambda : expr → bool
  | (lam a b c d) := tt
  | (var n) := ff
  | (sort l) := ff
  | (const a b) := ff
  | (mvar a b c) := contains_lambda c
  | (local_const a b c d) := contains_lambda d
  | (app a b) := contains_lambda a ∨ contains_lambda b
  | (pi a b c d) := contains_lambda c ∨ contains_lambda d
  | (elet a b c d) := contains_lambda c ∨ contains_lambda b ∨ contains_lambda d
  | (macro a b) := (b.map contains_lambda).foldr (λ x y, x ∨ y) ff

meta def is_first_order : expr → bool := λ e, ¬ (contains_lambda e ∨ contains_type_variables e)

meta def is_first_order_goal : tactic bool := target >>= (λ e, (return $ is_first_order e))

meta def is_first_order_goal_trace : tactic unit := is_first_order_goal >>= tactic.trace

-- example : (λ x : ℕ, x + 1) = λ x, 0 + x + 0 + 1  :=
-- begin
--  tidy? intro_ext_cfg, is_first_order_goal_trace
-- end

end is_first_order

section type_scraper

/-- Insert a into xs if a is not in xs -/
/- We use this to avoid duplicate types when instantiating -/
def cons_new {α : Type*} [decidable_eq α] (a : α) (xs : list α) : list α :=
  if a ∈ xs then xs else a :: xs

local infix `::'`:50 := cons_new

/-- Return a list of types which occur in the expr e -/
meta def types_in_expr  : expr →  tactic (list expr)
  | (lam a b c d) := do xs <- (types_in_expr d), return (c::'xs)
  | (var n) := return []
  | (sort l) := return []
  | (const a b) := return []
  | (mvar a b c) := types_in_expr c
  | (local_const a b c d) := types_in_expr d
  | (app a b) := do xs <- types_in_expr a, ys <- types_in_expr b, return (xs ++ ys)
  | (pi a b c d) := do xs <- (types_in_expr d), return (c::'xs)
  | (elet a b c d) := do xs <- types_in_expr b, ys <- types_in_expr d, return $ c::'(xs ++ ys)
  | (macro a b) := (b.map types_in_expr).mfoldr (λ x y, do x' <- x, return (x' ++ y)) []

meta def types_in_goal : tactic unit :=
  target >>= types_in_expr >>= tactic.trace

-- example : ∀ p : Prop, ∀ q : Prop, p ∧ q ↔ q ∧ p  :=
-- begin
--   types_in_goal,
-- end
end type_scraper

section preprocessor -- TODO
-- intended behavior: user calls it once and it attempts to perform rudimentary preprocessing and lambda-lifting. It fails if, at the end, the goal contains lambdas or pis. It will also attempt to instantiate quantifications over types in the assumptions if they are introduced.

meta def preprocess : tactic unit :=
do tgt                <- target,
   instantiation_list <- types_in_expr tgt
    -- trace instantiation_list
   >> lambda_set_tactic,
   do first_order_goal_flag <- is_first_order_goal,
      if first_order_goal_flag then return () else tactic.trace "Preprocessing failed, target is not first-order"

example : ∀ f : ℕ → ℕ, ∀ g : ℕ → ℕ → ℕ, (g $ f 0 ) 0 = (λ x y, g x y) (f 0) 0 ∧ ∀ p q : ℕ → Prop, ∀ r : Prop, (p 0) ↔ r ↔ ∀ r : Prop, (q 0) ↔ r
:=
begin
  preprocess, tidy, sorry
end

example : (λ x : ℕ, x + 1) = λ x, 0 + x + 0 + 1  :=
begin preprocess, simp end

-- TODO perform instantiations using congr_fun after applying extensionality lemmas

end preprocessor
  
end tactic