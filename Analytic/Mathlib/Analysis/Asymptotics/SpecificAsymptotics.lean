import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter

-- example {a b : ℕ} (h : a < b) :
--     (fun (x:ℝ) ↦ x^a) =o[atTop]  (fun x ↦ x^b) := by
--   exact isBig_pow_pow_atTop_of_le h

namespace Asymptotics

theorem isBigO_pow_pow_atTop_of_le {a b : ℕ} (h : a ≤ b) :
    (fun (x:ℝ) ↦ x^a) =O[atTop]  (fun x ↦ x^b) := by
  refine Eventually.isBigO ?_
  filter_upwards [Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop 0]
  intro x hx hx'
  simp only [norm_pow, Real.norm_of_nonneg hx']
  gcongr
  exact hx

end Asymptotics
