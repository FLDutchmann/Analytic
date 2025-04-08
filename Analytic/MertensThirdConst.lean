import Analytic.Mertens
import Analytic.Harmonic

open Filter Asymptotics Real Topology

open scoped Filter

noncomputable def zeta (x : ℝ) : ℝ := (riemannZeta x).re

theorem riemannZeta_ofReal (x : ℝ) : riemannZeta x = zeta x := by
  sorry
theorem riemannZeta_ofReal' (x : ℝ) (hx : 1 < x) : riemannZeta x = zeta x := by
  sorry

-- theorem test (f : ℕ → ℂ) (hf : ∀ n, (f n).im = 0) :

/- Surely there is a better way to do this?? -/
theorem Complex.tprod_ofReal {ι : Type*} (f : ι → ℝ) : ∏' n, (f n : ℂ) = ↑(∏' n, f n) := by
  by_cases h : Multipliable f
  · have := h.hasProd
    rw [HasProd] at this
    have hofReal := Complex.continuous_ofReal.tendsto (∏' n, f n)
    have := hofReal.comp this
    simp_rw [Function.comp_def, Complex.ofReal_prod] at this
    have : HasProd (fun n ↦ (f n : ℂ)) ↑(∏' n, f n) := this
    rw [this.tprod_eq]
  · rw [tprod_eq_one_of_not_multipliable h, tprod_eq_one_of_not_multipliable]
    · simp
    contrapose! h
    rw [Multipliable] at h ⊢
    obtain ⟨a, ha⟩ := h
    use a.re
    rw [HasProd] at ha ⊢
    have hre := Complex.continuous_re.tendsto a
    have := hre.comp ha
    simp_rw [← Complex.ofReal_prod, Function.comp_def, Complex.ofReal_re] at this
    exact this

theorem Real.zeta_eulerProd (x : ℝ) (hx : 1 < x) :
    zeta x = ∏' p : Nat.Primes, (1 - 1/(p:ℝ)^x)⁻¹ := by
  rw [zeta, ← riemannZeta_eulerProduct_tprod ?side]
  case side =>
    simp [hx]
  calc
  _ = (∏' (p : Nat.Primes), (↑(1 - p ^ (-x:ℝ) : ℝ)⁻¹ : ℂ)).re := by
    congr 2 with p
    push_cast
    congr
    rw [Complex.ofReal_cpow] <;> simp
  _ = _ := by
    rw [Complex.tprod_ofReal]
    simp only [Complex.ofReal_re, one_div]
    congr with p
    rw [Real.rpow_neg]
    simp

theorem zeta_pole_estimate_nhdsWithin :
    (fun σ:ℝ ↦ zeta (1+σ) - 1/σ) =O[𝓝[>] 0] (fun _ ↦ (1:ℝ)) := by
  have := (isBigO_riemannZeta_sub_one_div (F := ℝ))
  have tendsTo_ofReal : Tendsto Complex.ofReal (𝓝 1) (𝓝 1) := by
    apply Complex.continuous_ofReal.tendsto
  have := (this.comp_tendsto tendsTo_ofReal).mono (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have htt : Tendsto (fun σ ↦ 1 + σ) (𝓝[>] 0) (𝓝[>] 1) := by
    convert continuous_add_left (1:ℝ) |>.tendsto 0
    simp

  have := (this.comp_tendsto (k := fun σ ↦ 1 + σ) (l' := 𝓝[>] 0) ?_).congr'




  simp only [one_div, Function.comp_def, riemannZeta_ofReal] at this
  norm_cast at this
  ·
    simp


theorem euler_product {σ : ℝ} (hσ : 0 < σ) :
    zeta (1+σ) = ∏' p : Nat.Primes, (1 - 1 / ((p:ℝ)^(1+σ)))⁻¹ := by
  apply Real.zeta_eulerProd (1 + σ)
  linarith

theorem Real.log_zeta {σ : ℝ} (hσ : 0 < σ) :
    log (zeta (1+σ)) = ∑' p : Nat.Primes, log ((1 - 1/(p:ℝ)^(1+σ))⁻¹) := by
  rw [euler_product hσ]
  apply_fun exp
  · rw [Real.exp_log, Real.rexp_tsum_eq_tprod]
    · sorry
    · sorry
    · sorry
  · exact exp_injective

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
