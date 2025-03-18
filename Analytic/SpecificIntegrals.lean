import Mathlib

open MeasureTheory Real Filter


section loginv

/-- Computing the integral of $(x log^2 x)^{-1}$-/

theorem hasDerivAt_log_inv (x : ℝ) (hx : 1 < x): HasDerivAt (fun x ↦ (Real.log x)⁻¹)
    (- x⁻¹ * (Real.log x)⁻¹^2) x := by
  have hlog :
    HasDerivAt Real.log (x⁻¹) (x) := by
    convert Real.hasDerivAt_log (by linarith)
  convert (hasDerivAt_inv (Real.log_pos hx).ne.symm).comp x hlog using 1
  ring

theorem integrable_inv_mul_log_inv_sq (x : ℝ) (hx : 1 < x) :
    MeasureTheory.IntegrableOn (fun t ↦ t⁻¹ * (Real.log t)⁻¹ ^ 2)  (Set.Ici x) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have (t : ℝ) (ht : t ∈ Set.Ioi x) : HasDerivAt (fun x ↦ - (Real.log x)⁻¹)
      (t⁻¹ * (Real.log t)⁻¹^2) t := by
    simp only [Set.mem_Ioi] at ht
    convert (hasDerivAt_log_inv t (hx.trans ht)).neg using 1
    ring
  apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg _ this (l := 0)
  · simp only [Set.mem_Ioi]
    bound
  · rw [← neg_zero]
    apply (tendsto_inv_atTop_zero.comp tendsto_log_atTop).neg
  · refine ((continuousAt_log (by linarith)).continuousWithinAt).inv₀
      (Real.log_pos hx).ne.symm |>.neg

theorem setIntegral_Ioi_inv_mul_inv_log_sq (a : ℝ) (ha : 1 < a) :
    ∫ t in Set.Ioi a, t⁻¹ * (Real.log t)⁻¹ ^ 2 = (Real.log a)⁻¹ := by
  rw [show (Real.log a)⁻¹ = 0 - -(Real.log a)⁻¹ by ring]
  apply integral_Ioi_of_hasDerivAt_of_nonneg
  · apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.neg
    refine ContinuousAt.comp' ?_ ?_
    · refine continuousAt_inv₀ (Real.log_pos (by linarith)).ne.symm
    · refine continuousAt_log (by linarith)
  · intro x hx
    simp only [Set.mem_Ioi] at hx
    convert (hasDerivAt_log_inv _ _).neg using 1
    · ring
    · linarith
  · simp only [Set.mem_Ioi, inv_pow]
    bound
  · rw [← neg_zero]
    apply Tendsto.neg
    apply Tendsto.comp tendsto_inv_atTop_zero tendsto_log_atTop

end loginv

section loglog

theorem hasDerivAt_loglog (x : ℝ) (hx : 1 < x) : HasDerivAt (fun t ↦ Real.log (Real.log t))
    (x⁻¹ * (Real.log x)⁻¹) x := by
  rw [← Function.comp_def, mul_comm]
  apply (hasDerivAt_log (Real.log_pos hx).ne.symm).comp
  apply hasDerivAt_log (by linarith)

theorem integrable_inv_mul_log_inv_Icc (a b : ℝ) (ha : 1 < a):
    MeasureTheory.Integrable (fun t ↦ t⁻¹ * (Real.log t)⁻¹)
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
  rw [← MeasureTheory.IntegrableOn]
  have hsub : Set.Icc a b ⊆ {0}ᶜ := by
    simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and, not_le]
    intros
    linarith
  apply ((continuousOn_inv₀.mono hsub).mul ((continuousOn_log.mono hsub).inv₀ ?_))
    |>.integrableOn_compact isCompact_Icc
  intro x
  simp only [Set.mem_Icc, ne_eq, not_or, and_imp]
  -- bound
  intro hx _
  apply (Real.log_pos (by linarith)).ne.symm

theorem integral_inv_mul_invlog (a b : ℝ) (ha : 1 < a) (hb : a ≤ b) :
    ∫ (t : ℝ) in Set.Ioc a b, (t⁻¹ * (Real.log t)⁻¹) =
      Real.log (Real.log b) - Real.log (Real.log a) := by
  have hsub : Set.uIcc (3 / 2) b ⊆ {0}ᶜ := by
    simp only [Set.subset_compl_singleton_iff]
    refine Set.not_mem_uIcc_of_lt (by norm_num) (by linarith)
  have htzero : b ≠ 0 := by linarith
  have hlogzero : Real.log b ≠ 0 := (Real.log_pos (by linarith)).ne.symm
  rw [← intervalIntegral.integral_of_le hb]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x
    simpa only [hasDerivAt_loglog, Set.uIcc_of_le hb, Set.mem_Icc, and_imp] using
      fun h _ ↦ hasDerivAt_loglog _ (by linarith)
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  rw [Set.uIcc_of_le hb, MeasureTheory.IntegrableOn]
  exact integrable_inv_mul_log_inv_Icc a b ha

end loglog
