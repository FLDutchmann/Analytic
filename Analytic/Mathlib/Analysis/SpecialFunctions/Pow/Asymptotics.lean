import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open Real Topology NNReal ENNReal Filter ComplexConjugate Finset Set

theorem isBigO_rpow_rpow_atTop_of_le {a b : ℝ} (h : a ≤ b) :
    (fun (x:ℝ) ↦ x^a) =O[atTop] (fun x ↦ x^b) := by
  refine Eventually.isBigO ?_
  filter_upwards [Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop 0]
  intro x hx hx'
  simp only [norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  gcongr
  exact hx
