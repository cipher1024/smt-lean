import tactic.finish

open expr
namespace tactic

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

protected meta def lambda_set_core (a h : name) (v : expr) : tactic unit :=
do tp <- infer_type v,
   nv ← definev a tp v,
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
     -- trace "simp_hyp succeeded",
     interactive.simp_core_aux {} tactic.failed s [] [h] tt,
     tgt <- (target >>= pp),
     trace ("target after simp call is now... \n ⊢ " ++ (to_string (tgt)))

meta def lambda_set : expr → tactic unit
  | (var n) := return ()
  | (sort l) := return ()
  | (const a b) := return ()
  | (mvar a b c) := lambda_set c
  | (local_const a b c d) := lambda_set d 
  | (app a b) := lambda_set a >> lambda_set b
  | (lam a b c d) := do n <- (tactic.get_unused_name "HEWWO"),
                        n' <- (tactic.get_unused_name "HERRO"),
                        tactic.trace "lambda_set_core is being called again",
                        tactic.lambda_set_core n n' (lam a b c d)
  | (pi a b c d) := return ()
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

meta def lambda_set_tactic : tactic unit := do tgt <- target, lambda_set tgt
 
#check tactic.interactive.dsimp

example : (λ x : ℕ, x + 1) = λ x, 0 + x + 0 + 1  :=
begin
  lambda_set_tactic, simp[HEWWO, HEWWO_1],

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
Note: the call to the simplifier annoying simplifies other parts of the target along with the intended rewrite. Possible fix: using rw instead of simp? Or use expr.replace and then change?

Also todo: hook this up to a fragment of tidy or chain, to keep trying to apply extensionality lemmas. The example above is vacuous because we can get rid of the lambdas with funext
-/
end tactic
