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

-- TBD: right conditions on l
theorem est_log (f g : ℝ → ℝ)
    (hfg : (fun x ↦ f x - x⁻¹) =O[𝓝[>] 0] (fun _ ↦ (1:ℝ))) :
    (fun x ↦ log (f x) - log (x⁻¹)) =O[𝓝[>] 0] (fun x ↦ x) := by
  sorry


theorem est_1 : (fun σ ↦ log (zeta σ) - log (σ⁻¹)) =O[𝓝[>] 0] (fun σ ↦ σ) := by
  sorry

theorem est_2 : (fun σ ↦ log ((1-exp (-σ))⁻¹) - log (σ⁻¹)) =O[𝓝[>] 0] (fun σ ↦ σ) := by
  sorry

-- theorem est_3 : (fun σ ↦ log ((1-exp (-σ))⁻¹) - log (σ⁻¹)) =O[𝓟 (Set.Ici 0)] (fun σ ↦ σ) := by
--   sorry
-- noncomputable def logZeta (x : ℝ) : ℝ := Complex.log (riemannZeta x) |>.re

-- theorem im_zero {ι : Type*} (f : ι → ℂ)
--     (h : ∀ x, (f x).im = 0) : (∑' (p : ι), f p).im = 0 := by
--   by_cases hf : Summable f
--   · simp [Complex.im_tsum hf, h]
--   · simp [tsum_eq_zero_of_not_summable hf]


-- theorem logZeta_eq {x : ℝ} (hx : 1 < x) : logZeta x = ∑' (p : Nat.Primes), - Real.log (1 - ↑↑p ^ (-x)) := by exact_mod_cast calc
--   (logZeta x : ℂ) = _ := by
--     have : (∑' (p : Nat.Primes), -Complex.log (1 - ↑↑p ^ (-x : ℂ))).im = 0 := by
--       apply im_zero
--       intro p
--       simp [Complex.neg_im, neg_eq_zero, Complex.log_im, Complex.arg_eq_zero_iff, Complex.natCast_im]

--       sorry
--     rw [logZeta, ← riemannZeta_eulerProduct_exp_log (by simp [hx]), Complex.log_exp] <;> rw [this]
--     all_goals linarith only [pi_pos]
--   _ = (↑(∑' (p : Nat.Primes), - Real.log (1 - ↑↑p ^ (-x)):ℝ):ℂ) := by
--     stop
--     norm_cast
--     rw [Complex.re_tsum]
--     simp only [Complex.ofReal_neg, Complex.neg_re, Complex.log_ofReal_re]
--     sorry
--   -- sorry
