import Analytic.Mertens
import Analytic.Harmonic

open Filter Asymptotics Real


noncomputable def logZeta (x : ℝ) : ℝ := Complex.log (riemannZeta x) |>.re

theorem im_zero {ι : Type*} (f : ι → ℂ)
    (h : ∀ x, (f x).im = 0) : (∑' (p : ι), f p).im = 0 := by
  by_cases hf : Summable f
  · simp [Complex.im_tsum hf, h]
  · simp [tsum_eq_zero_of_not_summable hf]


theorem logZeta_eq {x : ℝ} (hx : 1 < x) : logZeta x = ∑' (p : Nat.Primes), - Real.log (1 - ↑↑p ^ (-x)) := by exact_mod_cast calc
  (logZeta x : ℂ) = _ := by
    have : (∑' (p : Nat.Primes), -Complex.log (1 - ↑↑p ^ (-x : ℂ))).im = 0 := by
      apply im_zero
      intro p
      simp [Complex.neg_im, neg_eq_zero, Complex.log_im, Complex.arg_eq_zero_iff, Complex.natCast_im]

      sorry
    rw [logZeta, ← riemannZeta_eulerProduct_exp_log (by simp [hx]), Complex.log_exp] <;> rw [this]
    all_goals linarith only [pi_pos]
  _ = (↑(∑' (p : Nat.Primes), - Real.log (1 - ↑↑p ^ (-x)):ℝ):ℂ) := by
    stop
    norm_cast
    rw [Complex.re_tsum]
    simp only [Complex.ofReal_neg, Complex.neg_re, Complex.log_ofReal_re]
    sorry
  -- sorry
