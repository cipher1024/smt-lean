import topology.basic data.set.intervals analysis.complex.exponential tactic.tidy «smt-lean»
open real set tactic

def twoco_interval := (Ioo (0:ℝ) 2)

noncomputable def simple_rational := function.restrict (λ (x:ℝ), 1/(x-2)) twoco_interval

open smt.logic_fragment
set_option trace.app_builder true

lemma simple_rational_of_twoco_items_are_nonzero :
  ∀ (a : subtype twoco_interval), a.val - 2 ≠ 0 :=
begin tidy,
veriT (AUFLIRA),
end
