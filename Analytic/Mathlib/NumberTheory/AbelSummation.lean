import Mathlib.NumberTheory.AbelSummation

noncomputable section

open Finset MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ}

namespace abelSummationProof

open intervalIntegral IntervalIntegrable

theorem _root_.sum_mul_eq_sub_sub_integral_mul'' (f' : ℝ → 𝕜) (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf_int : IntegrableOn f' (Set.Icc a b)) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - f a * (∑ k ∈ Icc 0 ⌊a⌋₊, c k) -
        ∫ t in Set.Ioc a b, f' t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  have deriv_eq : ∀ t ∈ Set.Icc a b, deriv f t = f' t := by
    simp only [Set.mem_Icc, and_imp] at hf_diff ⊢
    intro x hx hx'
    apply (hf_diff x hx hx').deriv
  convert _root_.sum_mul_eq_sub_sub_integral_mul c ha hab ?_ ?_ using 2
  · apply setIntegral_congr_fun
    · exact measurableSet_Ioc
    intro x hx
    simp_rw [deriv_eq x (Set.Ioc_subset_Icc_self hx)]
  · peel hf_diff with h using h.differentiableAt
  apply hf_int.congr_fun
  · exact Set.EqOn.symm deriv_eq
  exact measurableSet_Icc
