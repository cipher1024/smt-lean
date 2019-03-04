import tactic.finish tactic.tidy tactic.explode

namespace tactic
open expr tactic.interactive

section intro_ext

meta def intro_ext_tactics : list (tactic string) :=
[ -- tactic.reflexivity                                 >> pure "refl",
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

end intro_ext

section is_first_order
open level

meta def is_type : expr → bool
| (sort zero) := ff
| (sort (max l₁ l₂)) := tt
| (sort (succ l)) := tt
| (sort (param n)) := tt
| (sort (mvar n)) := tt
| e := ff

/- Checks if an an expr contains a quantification over types -/
meta def contains_type_variables : expr → bool
  | (lam a b c d) := is_type c ∨ contains_type_variables d
  | (var n) := ff
  | (sort l) := ff
  | (const a b) := ff
  | (mvar a b c) := contains_type_variables c
  | (local_const a b c d) := contains_type_variables d
  | (app a b) := contains_type_variables a ∨ contains_type_variables b
  | (pi a b c d) := is_type c ∨ contains_type_variables d
  | (elet a b c d) := is_type c ∨ contains_type_variables b ∨ contains_type_variables d
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

meta def is_lambda_free : tactic bool := target >>= (λ e, (return $ ¬ contains_lambda e))

meta def is_first_order : expr → bool := λ e, ¬ (contains_lambda e ∨ contains_type_variables e)

meta def is_first_order_goal : tactic bool := target >>= (λ e, (return $ is_first_order e))

meta def is_first_order_goal_trace : tactic unit := is_first_order_goal >>= tactic.trace

end is_first_order

section lambda_lifting

declare_trace lambda_set

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

protected meta def lambda_set_core' (a h : name) (v : expr) : tactic unit :=
-- do tactic.interactive.generalize h ":"
  do (e₁, e₂) <- generalize' h v a,
     h' <- get_local h,
     replace h ``(congr_fun %%h')

-- protected meta def lambda_set_core (a h : name) (v : expr) : tactic unit :=
-- do -- tp <- infer_type v,
--    nv ← pose a none v,
--    e <- (tactic.axiom_of_lambda nv v),
--    when_tracing `labda_set $ trace $ "new axiom is: " ++ (to_string e),
--    axm ← (tactic.axiom_of_lambda nv v) >>= assert h,
--    (intros >> tactic.interactive.refl) >> (when_tracing `lambda_set $ tactic.trace "intro + refl succeeded") <|> (when_tracing `lambda_set $ tactic.trace "intro + refl failed") <|> tactic.failed,
--    -- `[generalize : v = a]
--    pf ← to_expr ``(%%v = %%nv) >>= assert (h.append "_rw"),
--    reflexivity,
--      rw ← return pf,
--      when_tracing `lambda_set $ trace $ "new equality proof: " ++ (to_string pf),
--      s ← simp_lemmas.mk.add rw,
--      when_tracing `lambda_set $ trace $ "simp lemmas created successfully",
--      h::hs ← list.filter (λ e, e ≠ pf) <$> non_dep_prop_hyps,
--      when_tracing `lambda_set $ trace $ "hypotheses filtered successfully",
--      tgt <- target,
--      when_tracing `lambda_set $ trace $ "target is now: " ++ (to_string tgt),
--      target >>= pp >>=
--        (λ x, (when_tracing `lambda_set $ trace $ string.append "target before simp call is \n ⊢ " (to_string (x)))),
--      tactic.try $ interactive.simp_core_aux {eta := ff, beta := ff} (tactic.failed) s [] [h] tt,
--      target >>= pp >>=
--        (λ x, (when_tracing `lambda_set $ trace $ string.append "target after simp call is \n ⊢ " (to_string (x))))

meta def skip_if_lambda_free : tactic unit :=
is_lambda_free >>=
  λ b, if b then skip else tactic.fail "target still contains λ"

meta def lambda_set : expr → tactic unit
  | (var n) := return ()
  | (sort l) := return ()
  | (const a b) := return ()
  | (mvar a b c) := lambda_set c
  | (local_const a b c d) := lambda_set d 
  | (app a b) := lambda_set a >> lambda_set b
  | (lam a b c d) := -- (tidy intro_ext_cfg >>
  -- ((skip_if_lambda_free) <|> target >>= lambda_set)) <|>
                    (skip_if_lambda_free <|>
                    do n <- (tactic.get_unused_name "f"),
                       n' <- (tactic.get_unused_name "h_f"),
                       l <- pp (lam a b c d),
                        when_tracing `lambda_set $ trace "lambda_set_core is being called again",
                        when_tracing `lambda_set $ trace $ "rewrite target: " ++ (to_string l),
                        tactic.lambda_set_core' n n' (lam a b c d))
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

end lambda_lifting

section type_scraper

/-- Insert a into xs if a is not in xs -/
/- We use this to avoid duplicate types when instantiating -/
def cons_new {α : Type*} [decidable_eq α] (a : α) (xs : list α) : list α :=
  if a ∈ xs then xs else a :: xs

--note from Simon: use this instead of cons_new
-- #check native.rb_set.insert

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

end type_scraper

section instantiation
-- /-- A hypothesis can be applied if its type is a Pi-expr -/
meta def can_be_applied (e : expr) : tactic bool :=
 (infer_type e) >>= whnf >>= return ∘ is_pi 

/- Given the type of a function, get the type of the domain -/
meta def get_domain : expr → tactic expr
| (pi a b c d) := return c
| e := failed

meta def mk_appl_core (e₁ e₂ : expr) : tactic unit :=
do
   t <- infer_type e₁ >>= whnf >>= get_domain,
   (do infer_type e₂ >>= λ x, unify t x,
   -- e <- let e_app :=  in (to_expr ``(%%e_app)),
   get_unused_name ((to_string e₁)++(to_string e₂)) >>=
    λ n,  pose n none (app e₁ e₂), skip) <|> skip

meta def mk_appl_type_core (e₁ e₂ : expr) : tactic unit :=
do
   t <- infer_type e₁ >>= whnf >>= get_domain,
   (do infer_type e₂ >>= λ x, unify t x,
   -- e <- let e_app :=  in (to_expr ``(%%e_app)),
   get_unused_name ((to_string e₁)++(to_string e₂)) >>=
    λ n,  note n none (app e₁ e₂), skip) <|> failed

meta def mk_appl_type_core_flag (e₁ : expr) (l : list expr) : tactic bool :=
l.mfoldl (λ (b : bool) e₂,
           do b' <- (mk_appl_type_core e₁ e₂ >> return tt <|> return ff),
             return $ bor b b') ff

meta def mk_appls : tactic unit :=
do ls <- local_context,
   fs ← ls.mfilter can_be_applied,
   fs.mmap' (λ e₁, 
            try $ ls.mmap' (λ e₂, mk_appl_core e₁ e₂))

meta def mk_appls_type_variables (inst_list : list expr) : tactic unit :=
do ls <- local_context >>= λ x, return (x ++ inst_list),
   fs ← ls.mfilter (λ x, do b₁ <- can_be_applied x,
                      if b₁
                      then ((do t <- infer_type x, d <- get_domain t,
                                return (is_type d)) <|> return ff)
                      else return b₁),
   if fs = [] then failed else skip,
   fs.mmap' (λ e₁,  try $ ls.mmap' (λ e₂, mk_appl_type_core e₁ e₂)) >>
   fs.mmap' (λ e, try (clear e))

/-- this version of mk_apples_type_variables filters fs for successful applications
    and only clear successful applications -/
meta def mk_appls_type_variables' (inst_list : list expr) : tactic unit :=
do ls <- local_context >>= λ x, return (x ++ inst_list),
   fs ← ls.mfilter (λ x, do b₁ <- can_be_applied x,
                      if b₁
                      then ((do t <- infer_type x, d <- get_domain t,
                                return (is_type d)) <|> return ff)
                      else return b₁),
   if fs = [] then failed else skip,
   clear_list <- fs.mfilter (λ e, mk_appl_type_core_flag e ls),
   clear_list.mmap' $ try ∘ clear

meta def clear_type_quantifications : tactic unit :=
  do ls <- local_context,
     fs ← ls.mfilter (λ x, do b₁ <- can_be_applied x,
                        if b₁
                        then ((do t <- infer_type x, d <- get_domain t,
                                  return (is_type d)) <|> return ff)
                        else return b₁),
     if fs = [] then failed else skip,
     fs.mmap'(λ e, try (clear e))

end instantiation

section preprocessor -- TODO
/- Intended behavior: user calls it once and it attempts to perform rudimentary
  preprocessing and lambda-lifting.
  It fails if, at the end, the goal contains lambdas or quantifications over types.
  It will also attempt to instantiate quantifications over types in the assumptions
  if they are introduced. -/

meta def preprocess : tactic unit :=
do tidy intro_ext_cfg,
   tgt                <- target,
   instantiation_list <- types_in_expr tgt,
   lambda_set_tactic,
   repeat $ mk_appls_type_variables' instantiation_list,
   try $ clear_type_quantifications,
   do first_order_goal_flag <- is_first_order_goal,
      if first_order_goal_flag then return () else tactic.fail "Preprocessing failed, target is not first-order"

end preprocessor
end tactic

section test
open tactic

example : (λ x : ℕ, x + 1) = λ x, 0 + x + 0 + 1  :=
begin
  generalize h : (λ x : ℕ, x + 1) = g,
  generalize h' : (λ x : ℕ, 0 + x + 0 + 1) = g',
  finish
end

lemma hewwo : (λ x : ℕ, x + 1) = λ x, 0 + x + 0 + 1  :=
begin
  lambda_set_tactic, ext, finish
end

example : ∀ p : Prop, ∀ q : Prop, p ∧ q ↔ q ∧ p  :=
begin
  -- types_in_goal,
cc
end

-- set_option trace.lambda_set true
example : ∀ f : ℕ → ℕ, ∀ g : ℕ → ℕ → ℕ, (g $ f 0 ) 0 = (λ x y, g x y) (f 0) 0 -- ∧ ∀ p q : ℕ → Prop, ∀ r : Prop, (p 0) ↔ r ↔ ∀ r : Prop, (q 0) ↔ r
:=
begin
 preprocess, finish
end

example : ∀ α : Type, true ∧ (λ x : ℕ, x + 1) = λ x, 0 + x + 0 + 1  :=
begin tidy intro_ext_cfg, finish end

-- example : (∀ α : Type, true) ∧ true :=
-- begin
--   let f := λ y : ℕ, y + 1,
--   let x := (1 : ℕ),
--   let N := ℕ,
--   mk_appls, mk_appls, mk_appls,
--   do {b <- is_first_order_goal,
--     guard b},
-- end

example (F : Type → Type → ℕ) (α : Type) (G : Prop → Type) (q : Prop) (f : ℕ → ℕ) (k : ℕ) : unit :=
begin
/-
F : Type → ℕ,
α : Type,
G : Prop → Type,
q : Prop,
f : ℕ → ℕ,
k : ℕ
⊢ unit
-/
mk_appls_type_variables' [],
/-
α : Type,
G : Prop → Type,
q : Prop,
f : ℕ → ℕ,
k F.α : ℕ
⊢ unit
-/
mk_appls_type_variables' [],-- equivalent to repeat{mk_appls_type_variables []},
exact ()
-- α : Type,
-- G : Prop → Type,
-- q : Prop,
-- f : ℕ → ℕ,
-- k F.α.α : ℕ
-- ⊢ unit
end

end test
