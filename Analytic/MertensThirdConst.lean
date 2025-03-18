import Analytic.Mertens
import Analytic.Harmonic

open Filter Asymptotics Real


noncomputable def logZeta (x : ℝ) : ℝ := Complex.log (riemannZeta x) |>.re


example {x : ℝ} (hx : 1 < x) : logZeta x = ∑' (p : Nat.Primes), - Real.log (1 - ↑↑p ^ (-x)) := by exact_mod_cast calc
  (logZeta x : ℂ) = _ := by
    rw [logZeta, ← riemannZeta_eulerProduct_exp_log (by simp [hx]), Complex.log_exp]
    ·
      sorry
    · sorry
  _ = (↑(∑' (p : Nat.Primes), - Real.log (1 - ↑↑p ^ (-x)):ℝ):ℂ) := by
    sorry
  -- sorry
