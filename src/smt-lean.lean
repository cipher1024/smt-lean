import smt.basic
import smt.veriT

namespace smt.parser
open smt (atom sexpr)
open smt.atom

-- #eval nat.of_char ['1','2','3','0']


end smt.parser

namespace smt

open parser tactic ( unsafe_run_io )

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

namespace tactic.interactive

open smt (hiding expr) tactic smt.parser
open smt.sexpr smt.atom

-- | _ := fail "run_step"

open smt.logic_fragment (hiding hashable) tactic

-- -- Currently, QF_UF/QF_IDL/QF_RDL/QF_UFIDL are covered by proof production.
-- meta def insert_with {k α} (m : rb_map k α) (f : α → α → α) (x : k) (y : α) : rb_map k α :=
-- match m.find x with
-- | some y₀ := m.insert x (f y y₀)
-- | none := m.insert x y
-- end

-- meta def of_list_with {key data} [has_lt key] [decidable_rel $ @has_lt.lt key _] (f : data → data → data) :
--   list (key × data) → rb_map key data
-- | []           := native.rb_map.mk key data
-- | ((k, v)::ls) := insert_with (of_list_with ls) f k v

meta def hash_context : tactic word64 :=
do t ← target,
   (h,_) ← solve_aux t $ do {
     ls ← local_context,
     revert_lst ls,
     hash <$> target
     },
   pure h
open smt io io.process io.fs
meta def parse_log (fn : string) (prover : solver) : tactic prover.proof_type :=
do p ← tactic.unsafe_run_io $ io.fs.read_file fn,
   parser.run prover.read p

-- def cache {α} (f : unit → α) := trunc { x : option α // x.get_or_else (f ()) = f () }

-- def cache.mk {α} (f : unit → α) : cache f :=
-- trunc.mk ⟨ none,rfl ⟩

-- def cache.read {α} {f : unit → α} : cache f → α :=
-- trunc.lift (λ y : { s : option α // _ }, y.val.get_or_else (f ())) $
-- by { intros, casesm* [subtype _], simp *, }

-- lemma cache.read_eq  {α} {f : unit → α} (x : cache f) :
--   x.read = f () :=
-- trunc.induction_on x $
-- by { rintros ⟨ a, h ⟩, simp [cache.read,trunc.lift_beta,*], }

meta def unique_file_name (logic : logic_fragment) (prover : solver) (ext : string) : tactic string :=
do h ← hash_context,
   let h' := @hash_with_salt _ (prod.hashable _ _) (prover,logic) h,
   pure $ "proof_witness_" ++ to_string (h') ++ "." ++ ext

meta def write_formulas (logic : logic_fragment) (prover : solver) (xs : list string) (h : handle) : io unit :=
do let opts := prover.options ++ [
               "(set-option :produce-proofs true)",
               "(set-logic " ++ repr logic ++ ")"  ],
   opts.mmap' $ io.fs.put_str_ln h,
   xs.mmap' io.put_str,
   xs.mmap' $ io.fs.put_str h,
   io.fs.put_str_ln h "(check-sat)",
   io.fs.put_str_ln h "(get-proof)"

meta def mk_args (prover : solver) (fn : string) : list string :=
match prover.output_to_file with
| (some opt) := prover.args ++ [opt ++ fn]
| none := prover.args
end

meta def call_solver (logic : logic_fragment) (prover : solver) (fn : string) (xs : list string) : tactic string :=
unsafe_run_io $
do let args := mk_args prover fn,
   h ← io.proc.spawn
     { cmd := prover.cmd,
       args := args,
       stdin := stdio.piped,
       stdout := stdio.piped,
       stderr := stdio.piped },
   write_formulas logic prover xs h.stdin,
   close h.stdin,
   when (prover.output_to_file.is_none) $
     do { ln ← buffer.to_string <$> get_line h.stdout,
          io.put_str ln,
          file ← mk_file_handle fn mode.write,
          if ln = "unsat\n" then
          do proof ← read_to_end h.stdout,
             write file proof,
             io.put_str_ln proof.to_string
          else pure (),
          close file },
   -- xs ← buffer.to_string <$> read_to_end h.stdout,
   -- io.put_str_ln xs,
   xs ← buffer.to_string <$> read_to_end h.stderr,
   io.put_str_ln xs,
   proc.wait h,
   pure fn

open smt.logic_fragment
meta def veriT (logic : logic_fragment := QF_LIA) : tactic unit :=
do by_contradiction none,
   dedup,
   -- try $ `[norm_num at *],
   let prover := smt.veriT,
   -- `[dsimp only [has_pow.pow,pnat.pow,nat.pow,monoid.has_pow,gpow] { fail_if_unchanged := ff } ],
   fn ← unique_file_name logic prover "log",
   trace $ repr logic,
   trace fn,
   ls ← local_context,
   ps ← ls.mmap encode_local,
   unsafe_run_io $ do {
     h ← io.mk_file_handle fn mode.write,
     io.fs.write h "".to_char_buffer },
   fn ← call_solver logic prover fn ps,
   p ← parse_log fn prover,
   prover.execute p,
   done,
   pure ()

end tactic.interactive

