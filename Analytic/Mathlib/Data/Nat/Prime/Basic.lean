import Mathlib.Data.Nat.Prime.Basic

theorem pow_prime_iff (n k : ℕ) : Nat.Prime (n ^ k) ↔ n.Prime ∧ k = 1 := by
  constructor
  · intro h
    obtain rfl := Nat.Prime.eq_one_of_pow h
    simp_all
  · simp +contextual
