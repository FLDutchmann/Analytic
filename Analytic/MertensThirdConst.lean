import Analytic.Mertens
import Analytic.Harmonic

open Filter Asymptotics Real Topology

open scoped Filter

noncomputable def Real.zeta (x : ℝ) : ℝ := (riemannZeta x).re

theorem zeta_pole_estimate_nhdsWithin :
    (fun σ:ℝ ↦ zeta σ - 1/σ) =O[𝓝[>] 0] (fun _ ↦ (1:ℝ)) := by
  sorry

-- theorem zeta_pole_estimate_unif :
--     (fun σ:ℝ ↦ zeta σ - 1/σ) =O[𝓟 (Set.Ioi 0)] (fun _ ↦ (1:ℝ)) := by
--   sorry


theorem euler_product {σ : ℝ} (hσ : 0 < σ) :
    zeta σ = ∏' p : Nat.Primes, (1 - 1 / ((p:ℝ)^(1+σ)))⁻¹ := by
  sorry

theorem Real.log_zeta {σ : ℝ} (hσ : 0 < σ) :
    log (zeta σ) = ∑' p : Nat.Primes, log ((1 - 1/(p:ℝ)^(1+σ))⁻¹) := by
  sorry

private noncomputable def f (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (log ((1 - 1/(p:ℝ)^(1+σ))⁻¹) - 1 / (p : ℝ)^(1+σ))


theorem f_def' {σ : ℝ} (hσ : 0 < σ) : f σ = log (zeta (1+σ)) - ∑' (p : Nat.Primes), 1 / (p:ℝ) ^ (1+σ) := by
  sorry

theorem f_continuousOn : ContinuousOn f (Set.Ici 0) := by
  sorry

theorem f_zero : f 0 = mertens₃Const - mertens₂Const := by
  sorry

-- TBD: right conditions on l
theorem est_log (f g : ℝ → ℝ)
    (hfg : (fun x ↦ f x - x⁻¹) =O[𝓝[>] 0] (fun _ ↦ (1:ℝ))) :
    (fun x ↦ log (f x) - log (x⁻¹)) =O[𝓝[>] 0] (fun x ↦ x) := by
  sorry


theorem est_1 : (fun σ ↦ log (zeta σ) - log (σ⁻¹)) =O[𝓝[>] 0] (fun σ ↦ σ) := by
  sorry

theorem est_2 : (fun σ ↦ log ((1-exp (-σ))⁻¹) - log (σ⁻¹)) =O[𝓝[>] 0] (fun σ ↦ σ) := by
  sorry

theorem est_3 {σ : ℝ} (hσ : 0 < σ) : log ((1 - exp (- σ))⁻¹) = ∑' n : ℕ, exp (- σ * n) * (n : ℝ)⁻¹ := by
  sorry

/- This one's a little annoying. Use [1] to get the limit of the partial sums, then use [2] to get the value
of the tsum. https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/NatInt.html#Summable.tendsto_sum_tsum_nat

[1](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/AbelSummation.html#sum_mul_eq_sub_integral_mul₀)
[2](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/NatInt.html#Summable.tendsto_sum_tsum_nat)
-/
theorem est_4 {σ : ℝ} (hσ : 0 < σ) :
    ∑' n : ℕ, exp (- σ * n) * (n : ℝ)⁻¹ = σ * ∫ t in Set.Ioi 0, exp (- σ * t) * harmonic (⌊t⌋₊) := by
  sorry


theorem est_log_zeta :
    (fun σ ↦ log (zeta (1 + σ)) - σ * ∫ t in Set.Ioi 1, exp (- σ * t) * harmonic (⌊t⌋₊)) =O[𝓝[>] 0] (fun σ ↦ σ) := by
  sorry

noncomputable def P (t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesBelow ⌊t⌋₊, (p : ℝ)⁻¹

theorem est_P {σ : ℝ} (hσ : 0 < σ) :
    ∑' p : Nat.Primes, (p : ℝ)⁻¹ ^(1+σ) = σ * ∫ t in Set.Ioi 0, exp (- σ * t) * P (exp t) := by
  sorry

theorem est_f :
    (fun σ ↦ f σ - σ * ∫ t in Set.Ioi 0, exp (- σ * t) * (harmonic ⌊t⌋₊ - P (exp t))) =O[𝓝[>] 0] (fun σ ↦ σ) := by
  sorry

theorem harmonic_est :
    (fun t ↦ harmonic (⌊t⌋₊) - (log t - eulerMascheroniConstant)) =O[𝓟 (Set.Ici 1)] fun t ↦ t⁻¹ := by
  sorry


theorem P_exp_est :
    (fun t ↦ P (exp t) - (log t - mertens₂Const)) =O[𝓟 (Set.Ici 1)] fun t ↦ t⁻¹ := by
  sorry

theorem f_zero' :
    f 0 = eulerMascheroniConstant - mertens₂Const := by
  sorry

theorem mertens₃Const_eq : mertens₃Const = eulerMascheroniConstant := by
  sorry
