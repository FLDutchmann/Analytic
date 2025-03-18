import Mathlib.Analysis.Asymptotics.Lemmas

open Filter Asymptotics

/- https://github.com/leanprover-community/mathlib4/pull/23055 -/
theorem isBigO_nat_of_isBigO_atTop {f g : ℕ → ℝ} (hfg : f =O[atTop] g) (l : Filter ℕ)
    (h : ∀ᶠ n in l, g n = 0 → f n = 0) : f =O[l] g := by
  obtain ⟨C, hC_pos, hC⟩ := Asymptotics.bound_of_isBigO_nat_atTop hfg
  refine isBigO_iff.mpr ?_
  use C
  filter_upwards [h] with x h
  by_cases hf : f x = 0
  · simp [hf, hC_pos]
  apply hC
  exact fun a ↦ hf (h a)
