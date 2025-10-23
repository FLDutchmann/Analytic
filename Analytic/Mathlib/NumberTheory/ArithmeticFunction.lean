import Mathlib.NumberTheory.ArithmeticFunction

open Nat ArithmeticFunction zeta

theorem ArithmeticFunction.sum_range_mul_zeta
    {R : Type*} [Semiring R] (f : ArithmeticFunction R) (N : ℕ) :
    ∑ d ∈ Finset.range (N + 1), (f * ζ) d = ∑ d ∈ Finset.range (N + 1), (N / d) • f d := by
  induction N with
  | zero => simp
  | succ n h_ind =>
    rw [Finset.sum_range_succ]
    simp_rw [Nat.succ_div, add_smul, Finset.sum_add_distrib, h_ind]
    congr 1
    · apply Finset.sum_subset
      · grind
      · simp only [Finset.mem_range, not_lt, nsmul_eq_mul]
        intro d hd1 hd2
        obtain rfl : d = n+1 := by omega
        apply mul_eq_zero_of_left
        convert cast_zero
        simp only [Nat.div_eq_zero_iff, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
          lt_add_iff_pos_right, zero_lt_one, or_true]
    · simp_rw [boole_smul, ← Finset.sum_filter]
      rw [Nat.filter_dvd_eq_divisors (add_one_ne_zero n)]
      exact coe_mul_zeta_apply
