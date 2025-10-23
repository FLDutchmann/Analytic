/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib

import Analytic.SpecificIntegrals

import Analytic.Mathlib.MeasureTheory.Integral.Asymptotics
import Analytic.Mathlib.MeasureTheory.Integral.SetIntegral
import Analytic.Mathlib.NumberTheory.AbelSummation
import Analytic.Mathlib.NumberTheory.ArithmeticFunction
import Analytic.Mathlib.Data.Nat.Prime.Basic
import Analytic.Mathlib.Analysis.Asymptotics.Defs
import Analytic.Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Analytic.ForMathlib.EquivalentLogExp

open Filter Nat Real Finset
open Asymptotics
open MeasureTheory

set_option linter.style.longLine false

attribute [bound] tsum_nonneg ArithmeticFunction.vonMangoldt_nonneg sum_nonneg integral_nonneg
section fun_prop
attribute [fun_prop] measurable_log Measurable.aestronglyMeasurable
end fun_prop

open scoped ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt

axiom hpsi_cheby : (fun n => ∑ k ∈ Finset.range (n+1), Λ k) =O[atTop] (fun n ↦ (n:ℝ))

section MertensFirst

theorem log_stirling' :
  Tendsto (fun n => Real.log (n)!
    - (n * Real.log n - n + Real.log n / 2 + Real.log π / 2 + Real.log 2 / 2))
    atTop (nhds 0) := by
  rw [← Asymptotics.isLittleO_one_iff ℝ, ← Asymptotics.isEquivalent_exp_iff_sub_isLittleO_one]
  have :=  Stirling.factorial_isEquivalent_stirling
  apply this.congr_left _ |>.congr_right
  · filter_upwards [eventually_gt_atTop 0] with n hn
    simp_rw [add_assoc, ← add_div]
    rw [exp_add, exp_sub, Real.exp_nat_mul, div_pow, ← exp_nat_mul, exp_log,
      ← log_mul, ←log_mul, ← log_sqrt, exp_log] <;> try positivity
    ring_nf
  · filter_upwards with n
    rw [exp_log]
    positivity

theorem log_stirling :
  Tendsto (fun n => Real.log (n)!
    - (n * Real.log n - n + Real.log n / 2 + Real.log π / 2 + Real.log 2 / 2))
    atTop (nhds 0) := by
  have :=  Stirling.factorial_isEquivalent_stirling
  rw [← Asymptotics.isEquivalent_iff_log_sub_log] at this
  case hf =>
    filter_upwards with x
    norm_cast
    apply factorial_pos
  case hg =>
    filter_upwards [eventually_gt_atTop 0] with x hx
    positivity
  rw [← Asymptotics.isLittleO_one_iff ℝ]
  apply this.congr' _ (by rfl)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.log_mul, Real.log_sqrt, Real.log_mul, Real.log_mul, Real.log_pow,
    Real.log_div, Real.log_exp] <;> try positivity
  ring


/- One pain point I'm running into here is finding the right theorems in the library - say I need a
IsBigO statement but it's phrased as IsLittleO in the library. Things like natCast_atTop also make
exact? and the like less useful.
-/
theorem log_fac_sub_id_mul_log_isBigO_id :
    (fun n ↦ Real.log (n !) - n * Real.log n) =O[atTop] (fun n ↦ (n:ℝ)) := by
  have hstirling := log_stirling
  rw [← Asymptotics.isLittleO_one_iff ℝ] at hstirling
  have : (fun _ ↦ 1 : ℝ → ℝ) =O[atTop] (fun x ↦ (x : ℝ)) := by
    convert isBigO_pow_pow_atTop_of_le zero_le_one with x
    simp
  have const_isBigO (c : ℝ) : (fun (_ : ℕ) ↦ c) =O[atTop] (fun (n : ℕ) ↦ (n : ℝ)) := by
    convert (this.const_mul_left c).natCast_atTop
    simp only [mul_one]
  have hlarger := hstirling.isBigO.trans (const_isBigO 1).natCast_atTop
  simp only [← sub_sub, ← sub_add] at hlarger
  rw [IsBigO.sub_iff_left (by exact const_isBigO _), IsBigO.sub_iff_left (by exact const_isBigO _),
    IsBigO.sub_iff_left, IsBigO.add_iff_left] at hlarger
  · exact hlarger
  · exact Asymptotics.isBigO_refl (α := ℕ) (fun n ↦ (n:ℝ)) atTop
  · apply (Real.isLittleO_log_id_atTop.isBigO.const_mul_left (1/2:ℝ)).natCast_atTop.congr_left
    bound

theorem ArithmeticFunction.tmp
    {R : Type*} [Ring R] (f : ArithmeticFunction R) (N : ℕ) :
    ∑ d ∈ Finset.range (N + 1), (f * ζ) d = ∑ d ∈ Finset.range (N + 1), Int.floor (N / d : ℚ) • f d := by
  convert ArithmeticFunction.sum_range_mul_zeta f N using 1
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mem_range] at hd
  simp [zsmul_eq_mul, nsmul_eq_mul]
  rw [Rat.floor_natCast_div_natCast]
  norm_cast

theorem Real.log_factorial (n : ℕ) :
  Real.log (n)! = ∑ k ∈ Finset.range (n+1), Real.log k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by norm_cast)
      (mod_cast Nat.factorial_ne_zero n), sum_range_succ, add_comm, ih]

theorem log_factorial (n : ℕ) :
  Real.log (n)! = ∑ d ∈ Finset.range (n+1), ⌊(n / d : ℚ)⌋ * Λ d := by
  simp_rw [Real.log_factorial, ← ArithmeticFunction.log_apply,
    ← ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.tmp, zsmul_eq_mul]

theorem sum_floor_mul_vonmangoldt (n : ℕ) : ∑ d ∈ Finset.range (n+1), ↑⌊(n / d : ℚ)⌋ * Λ d =
  n * ∑ d ∈ Finset.range (n+1), Λ d / d + ∑ d ∈ Finset.range (n+1), (-Int.fract (n / d : ℚ)) * Λ d := by
  rw [mul_sum, ← sum_add_distrib, ]
  simp_rw [← Int.self_sub_floor]
  congr 1 with d
  push_cast
  ring

theorem sum_integer_mul_vonMangoldt : (fun n ↦ ∑ d ∈ Finset.range (n+1), (- Int.fract (n/d: ℚ)) * Λ d)
    =O[atTop] (fun n ↦ (n : ℝ)) := by
  calc
    _ =O[atTop] (fun n ↦ ∑ d ∈ Finset.range (n+1), 1 * Λ d)  := by
      apply Filter.Eventually.isBigO
      filter_upwards
      intro n
      simp only [norm_eq_abs]
      apply (abs_sum_le_sum_abs ..).trans _
      gcongr with d hd
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      gcongr
      · exact ArithmeticFunction.vonMangoldt_nonneg
      · simp only [Rat.cast_fract, Rat.cast_div, Rat.cast_natCast, abs_neg, Int.abs_fract]
        apply Int.fract_lt_one _ |>.le
    _ =O[atTop] _ := by
      simp only [one_mul]
      exact hpsi_cheby

-- n! = ∏ k ≤ n, n.factorization.prod fun p i => p ^ i = ∏ k ≤ n, ∏ p in primesBelow n, p ^ (Nat.factorization k n)
-- Nat.prod_factorization_eq_prod_primeFactors ()
theorem sum_cheby_div_id :
  (fun n : ℕ ↦ (∑ k ∈ Finset.range (n+1), Λ k / k) - Real.log n) =O[atTop] fun _ ↦ (1:ℝ) := by
  have : (fun n ↦ n * ∑ d ∈ Finset.range (n+1), Λ d / d - n * Real.log n) =O[atTop]
      (fun n ↦ (n:ℝ)) := by
    have := log_fac_sub_id_mul_log_isBigO_id
    simp_rw [_root_.log_factorial, sum_floor_mul_vonmangoldt] at this
    convert this.sub sum_integer_mul_vonMangoldt using 2 with n
    ring
  apply this.mul (isBigO_refl (fun (n : ℕ) ↦ (n : ℝ)⁻¹) atTop) |>.congr'
  · filter_upwards [eventually_gt_atTop 0]
    intro x hx
    field
  · filter_upwards [eventually_ne_atTop 0]
    intro x hx
    field_simp

theorem sq_isBigO_id_mul_sub_one : (fun x ↦ x^2) =O[atTop] fun x:ℝ ↦ x * (x - 1) := by
  let P : Polynomial ℝ := .X^2
  let Q : Polynomial ℝ := .X * (.X - 1)
  convert Polynomial.isBigO_of_degree_le P Q ?_ with x x <;> simp only [P, Q]
  · simp
  · simp
  convert_to (Polynomial.X^2).degree ≤ 2 using 1
  · compute_degree
    · norm_num
    · decide
  compute_degree

theorem mul_sub_one_inv_isBigO_neg_two :
    (fun x:ℝ ↦ (x * (x - 1))⁻¹) =O[atTop] fun x ↦ x^(-2:ℝ) := by
  apply (sq_isBigO_id_mul_sub_one.inv_rev _).congr'
  · rfl
  · filter_upwards [eventually_ge_atTop 0]
    intro x hx
    rw [rpow_neg hx]
    norm_num
  filter_upwards [eventually_ne_atTop 0] with a ha ha'
  simp_all

theorem isBigO_fun : (fun x ↦ Real.log x / (x * (x - 1)))
    =O[atTop] fun x ↦ x ^ (-3 / 2:ℝ) := by
  have hlog := isLittleO_log_rpow_atTop (show 0 < (1/2:ℝ) by norm_num)
  have hpoly : (fun x ↦ x^2) =O[atTop] fun x:ℝ ↦ x * (x - 1) := sq_isBigO_id_mul_sub_one
  have := mul_sub_one_inv_isBigO_neg_two
  apply (hlog.isBigO.mul this).congr'
  · simp_rw [div_eq_mul_inv]
    rfl
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp_rw [← rpow_add hx]
    norm_num

theorem sum_strictPow_convergent :
    Summable (fun (n:ℕ) ↦ if ¬ Nat.Prime n then Λ n / n else 0) := by
  convert_to Summable ({k : ℕ | IsPrimePow k}.indicator
    fun (n:ℕ) ↦ if ¬ Nat.Prime n then Λ n / n else 0)
  · ext n
    by_cases h : IsPrimePow n
    · simp [h]
    · simp [h, ArithmeticFunction.vonMangoldt_eq_zero_iff]
  rw [← summable_subtype_iff_indicator]
  have hassum_p (p : Primes) :
      HasSum (fun y => if y = 0 then 0 else Real.log p / p^(y+1)) (Real.log p / (p * (p-1))) := by
    have hp : (p : ℝ) ≠ 0 := by
      exact_mod_cast p.2.ne_zero
    have hp' : (p : ℝ)⁻¹ ≠ 0 := by
      exact inv_ne_zero hp
    rw [← hasSum_nat_add_iff' 1]
    simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, range_one,
      sum_singleton, sub_zero, div_eq_mul_inv, ]
    rw [hasSum_mul_left_iff (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne.symm, ]
    simp_rw [← inv_pow, pow_succ]
    rw [show (p * (p - 1 : ℝ))⁻¹ = (1-(p:ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ from ?rw]
    case rw =>
      rw [← mul_inv, sub_mul]
      simp only [mul_inv_rev, one_mul, isUnit_iff_ne_zero, ne_eq, hp,
        not_false_eq_true, IsUnit.inv_mul_cancel]
    rw [hasSum_mul_right_iff hp', hasSum_mul_right_iff hp']
    apply hasSum_geometric_of_lt_one (r := (p:ℝ)⁻¹) (by positivity)
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast p.2.one_lt
  set f := (fun (n:ℕ) ↦ if ¬ Nat.Prime n then Λ n / n else 0) ∘
    (fun x : {k : ℕ | IsPrimePow k} ↦ (x : ℕ))
  let e := Nat.Primes.prodNatEquiv
  erw [← Equiv.summable_iff e]
  have : f ∘ e = fun p ↦ if p.2 = 0 then 0 else Real.log p.1 / p.1 ^ (p.2+1) := by
    ext ⟨p, k⟩
    simp +contextual [Set.coe_setOf, ite_not, Function.comp_apply,
      Primes.prodNatEquiv_apply, pow_prime_iff, Subtype.property, true_and, cast_pow,
      f, e, ArithmeticFunction.vonMangoldt_apply_pow, ArithmeticFunction.vonMangoldt_apply_prime]
  rw [this, summable_prod_of_nonneg]
  · refine ⟨?_, ?_⟩
    · intro p
      apply (hassum_p p).summable
    simp_rw [fun p : Primes ↦ (hassum_p p).tsum_eq]
    simp [Primes]
    -- need Nat not Primes...
    -- -- why do I need to give f here...
    -- apply Summable.comp_injective (i := (fun p : Primes ↦ (p : ℕ)))
    --   (f := fun (n: ℕ) => Real.log n / (n * (n - 1:ℝ)) )
    apply summable_of_isBigO (g := fun p : Primes ↦ (p:ℝ) ^ (-3/2:ℝ))
    · rw [Nat.Primes.summable_rpow]
      norm_num
    convert_to (((fun x ↦ Real.log x / (x * (x-1))) ∘ (fun n : ℕ ↦ (n : ℝ))) ∘
      (fun p : Primes ↦ (p : ℕ)))
      =O[cofinite] (((fun x ↦ x^(-3/2:ℝ)) ∘ (fun n : ℕ ↦ (n : ℝ))) ∘ (fun p : Primes ↦ (p : ℕ)))
    apply Asymptotics.IsBigO.comp_tendsto (l := cofinite)
    · rw [Nat.cofinite_eq_atTop]
      exact Asymptotics.IsBigO.comp_tendsto isBigO_fun tendsto_natCast_atTop_atTop
    · apply Function.Injective.tendsto_cofinite Primes.coe_nat_injective
  · intro p
    simp only [Pi.zero_apply]
    positivity

theorem sum_primesBelow_log_div_id_eq_vonMangoldt_sub (n : ℕ) :
  ∑ p ∈ primesBelow (n+1), Real.log p / p = ∑ k ∈ Finset.range (n+1), Λ k / k
    - ∑ k ∈ Finset.range (n+1), if ¬ Nat.Prime k then Λ k / k else 0 := by
  trans ∑ p ∈ primesBelow (n+1), Λ p / p
  · apply sum_congr rfl
    simp +contextual [mem_primesBelow, ArithmeticFunction.vonMangoldt_apply_prime]
  rw [eq_sub_iff_add_eq, ← Finset.sum_filter, ← Finset.sum_union]
  · apply sum_subset <;>
    · intro a
      simp +contextual only [mem_union, mem_primesBelow, mem_filter, mem_range]
      tauto
  · rw [Finset.disjoint_left]
    simp +contextual only [mem_primesBelow, mem_filter, mem_range, not_true_eq_false, and_false,
      not_false_eq_true, implies_true]

theorem sum_properPower_vonMangoldt_div_id_isBigO_one :
  (fun n ↦ ∑ k ∈ Finset.range (n+1), if ¬ Nat.Prime k then Λ k / k else 0) =O[atTop]
    (fun _ ↦ (1 : ℝ)) := by
  apply Filter.IsBoundedUnder.isBigO_one
  use (∑' (n:ℕ), if ¬ Nat.Prime n then Λ n / n else 0)
  simp only [norm_eq_abs, eventually_map]
  filter_upwards with a
  rw [abs_of_nonneg ?pos]
  case pos =>
    bound
    -- apply Finset.sum_nonneg
    -- intro k __
    -- have := ArithmeticFunction.vonMangoldt_nonneg (n:=k)
    -- positivity
  apply Summable.sum_le_tsum (Finset.range (a+1)) _ (sum_strictPow_convergent)
  bound
  -- intro k _
  -- have := ArithmeticFunction.vonMangoldt_nonneg (n:=k)
  -- positivity

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

theorem mertens_first : (fun n : ℕ ↦ (∑ p ∈ primesBelow (n+1), Real.log p / p) - Real.log n)
    =O[⊤] (fun _ ↦ (1 : ℝ)) := by
  apply isBigO_nat_of_isBigO_atTop ?A _ ?B
  case B =>
    filter_upwards with _
    exact fun h ↦ (one_ne_zero h).elim
  simp_rw [sum_primesBelow_log_div_id_eq_vonMangoldt_sub]
  have h₀ := sum_properPower_vonMangoldt_div_id_isBigO_one
  have h₁ := sum_cheby_div_id
  apply (h₁.sub h₀).congr <;>
  · intro x
    ring
set_option linter.style.longLine false

@[reducible]
private noncomputable def E₁ (t : ℝ) : ℝ :=
  (∑ p ∈ primesBelow (⌊t⌋₊+1), Real.log p / p) - Real.log t

private theorem E₁_eq : E₁ = fun t ↦ (∑ p ∈ primesBelow (⌊t⌋₊+1), Real.log p / p) - Real.log t :=
  rfl

theorem E₁_eq_add (t : ℝ) : (∑ p ∈ primesBelow (⌊t⌋₊+1), Real.log p / p) = Real.log t + E₁ t := by
  rw [E₁_eq]
  ring

theorem E₁_of_lt_two (t : ℝ) (ht_nonneg : 0 ≤ t) (ht : t < 2) : E₁ t = - Real.log t := by
  have : ⌊t⌋₊ ≤ 1 := by
    apply Nat.le_of_lt_succ
    rw [Nat.floor_lt ht_nonneg]
    exact ht
  have : (⌊t⌋₊ + 1).primesBelow = ∅ := by
    ext p
    simp [mem_primesBelow]
    intro h hp
    have := hp.two_le
    omega
  rw [E₁, this, Finset.sum_empty, zero_sub]

@[fun_prop, measurability]
theorem E₁_measurable : Measurable E₁ := by
  rw [E₁_eq]
  apply Measurable.sub
  · apply (measurable_from_nat (f := fun n ↦ ∑ p ∈ primesBelow (n+1), Real.log p / p)).comp
      Nat.measurable_floor
  · fun_prop

theorem Asymptotics.IsBigO.nat_floor {f g : ℕ → ℝ} (h : f =O[⊤] g) :
  (fun x ↦ f (Nat.floor x)) =O[⊤] (fun x ↦ (g (Nat.floor x)) : ℝ → ℝ) := by
  apply h.comp_tendsto tendsto_top

open Filter
theorem antitoneOn_id_div_sub : AntitoneOn (fun x : ℝ ↦ x / (x-1)) (Set.Ioi 1) := by
  have := (sub_inv_antitoneOn_Ioi (c:=(1:ℝ))).add_const 1
  apply this.congr
  intro x hx
  simp only [Set.mem_Ioi] at hx
  apply Eq.symm
  calc _ = ((x-1) + 1)/(x-1) := by ring
    _ = _ := by
      rw [_root_.add_div, div_self (by linarith)]
      ring

@[bound]
theorem floor_pos_of {α : Type* } [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α]
    {a : α} (h : 1 ≤ a) :  0 < ⌊a⌋₊ := by
  apply Nat.floor_pos.mpr h

attribute [bound] Nat.floor_le
-- ouchie
/- There should be some general theorem: given f : ℕ → ℝ and g h : ℝ → ℝ, got from f n - g n =O h n
 to f ⌊x⌋₊ - g x =O h x under certain "smoothnes"/monotonicity assumptions on g -/
theorem E₁_isBigO_one {t : ℝ} (ht : 1 < t) : E₁ =O[𝓟 <| Set.Ici t] (fun _ ↦ (1:ℝ)) := by
  have h₀ : (fun t ↦ Real.log t - Real.log (⌊t⌋₊)) =O[𝓟 <| Set.Ici t]
      (fun t ↦ Real.log t - Real.log (t-1)) := by
    have h1 (t : ℝ) (ht : 1 < t) : Real.log (t-1) ≤ Real.log (⌊t⌋₊) := by
      bound [Nat.lt_floor_add_one t]
    have h2 (t : ℝ) (ht : 1 ≤ t) : Real.log (⌊t⌋₊) ≤ Real.log t := by
      bound
    apply Eventually.isBigO
    simp only [norm_eq_abs, eventually_principal, Set.mem_Ici]
    intro t ht
    rw [abs_of_nonneg (by bound)] --; linarith only [h2 t (by linarith)])]
    gcongr
    · linarith
    · linarith only [Nat.lt_floor_add_one t]
  have h₁ : (fun t ↦ Real.log t - Real.log (t-1)) =O[𝓟 <| Set.Ici t] (fun _ ↦ (1:ℝ)) := by
    apply IsBigO.trans _ (Asymptotics.isBigO_const_const (t/(t-1)) one_ne_zero _)
    apply Filter.Eventually.isBigO
    simp only [norm_eq_abs, eventually_principal, Set.mem_Ici]
    intro x hx
    rw [abs_of_nonneg ?nonneg]
    case nonneg =>
      rw [sub_nonneg]
      gcongr <;> linarith
    rw [← Real.log_div]
    · apply (Real.log_le_self _).trans
      · apply antitoneOn_id_div_sub _ _ hx <;> simp only [Set.mem_Ioi, ht]
        linarith
      bound
      -- apply div_nonneg (by linarith)
      -- linarith
    · linarith
    · exact sub_ne_zero_of_ne (by linarith)
  simp_rw [E₁_eq]
  apply ((mertens_first.mono le_top).nat_floor.mono le_top |>.sub (h₀.trans h₁)).congr <;>
  · intro x
    ring

end MertensFirst

section MertensSecond

theorem Icc_filter_prime (n : ℕ) :
    filter (fun a ↦ Nat.Prime a) (Icc 0 n) = Nat.primesBelow (n+1) := by
  ext p
  simp only [mem_filter, mem_Icc, _root_.zero_le, true_and, mem_primesBelow, and_congr_left_iff]
  omega

theorem helper1 (n : ℕ) :
    ∑ x ∈ Icc 0 n, (if Nat.Prime x then Real.log ↑x / ↑x else 0) =
    ∑ p ∈ (n+1).primesBelow, Real.log p / p := by
  rw [← sum_filter, sum_congr]
  · ext p
    simp only [mem_filter, mem_Icc, _root_.zero_le, true_and, mem_primesBelow, and_congr_left_iff]
    omega
  · simp only [implies_true]


theorem mul_E₁_measurable : Measurable (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2 * E₁ a) := by
  fun_prop

theorem integrableOn_Ici_fun_mul_E₁ (t : ℝ) (ht : 1 < t) :
    MeasureTheory.IntegrableOn (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2 * E₁ a) (Set.Ici t) := by
  have isBigO : (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2 * E₁ a) =O[𝓟 (Set.Ici t)]
      (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2) := by
    simp_rw [mul_assoc]
    convert (isBigO_refl (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2) _).mul (E₁_isBigO_one ht) using 1
    · ext; ring
    · ext; ring
  have hmg : (𝓟 (Set.Ici t)).IsMeasurablyGenerated := principal_isMeasurablyGenerated_iff.mpr
    measurableSet_Ici
  have := isBigO.integrableAtFilter («μ» := volume)
    mul_E₁_measurable.stronglyMeasurable.stronglyMeasurableAtFilter
    (integrable_inv_mul_log_inv_sq t ht).integrableAtFilter
  rw [_root_.integrableAtFilter_principal_iff] at this
  exact this

theorem integral_mul_E₁_eq_const_sub_integral (x a : ℝ) (ha : 1 < a) (hx : a ≤ x) :
    ∫ (t : ℝ) in Set.Icc a x, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t =
    (∫ (t : ℝ) in Set.Ioi a, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t)
    - ∫ (t : ℝ) in Set.Ioi x, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t := by
  rw [eq_sub_iff_add_eq, ← setIntegral_union]
  · rw [← integral_Ici_eq_integral_Ioi]
    congr
    refine Set.Icc_union_Ioi_eq_Ici hx
  · rw [Set.disjoint_iff]
    intro t
    simp
  · measurability
  · apply (integrableOn_Ici_fun_mul_E₁ a ha).mono Set.Icc_subset_Ici_self le_rfl
  · apply (integrableOn_Ici_fun_mul_E₁ a ha).mono (Set.Ioi_subset_Ici hx) le_rfl

-- example {ι : Type*} {f g : ℝ → ℝ} (a : ℝ) (hg : ∀ x, 0 ≤ g x) (hfg : f =O[𝓟 (Set.Ioi a)] g) :
--     (fun x ↦ ∫ t in Set.Ioi x, f t) =O[𝓟 (Set.Ioi a)] (fun x ↦ ∫ t in Set.Ioi x, g t) := by
--   rw [isBigO_iff]
--   obtain ⟨C, _, hC⟩ := hfg.exists_pos
--   rw [isBigOWith_iff] at hC
--   use C
--   simp only [norm_eq_abs, eventually_principal, Set.mem_Ioi] at hC ⊢
--   intro x hx
--   -- filter_upwards [hC] with x hC'
--   rw [abs_of_nonneg (a := ∫ x in _, g x) (by bound), ← integral_const_mul]
--   apply abs_integral_le_integral_abs.trans
--   have hg_integ : IntegrableOn g (Set.Ioi a) volume := by
--     sorry
--   apply setIntegral_mono_on
--   · apply (hfg.abs_left.integrableOn (Set.Ioi a) ..).mono_set
--     · refine Set.Ioi_subset_Ioi hx.le
--     · exact measurableSet_Ioi
--     · sorry
--     · apply hg_integ
--   · apply Integrable.const_mul
--     rw [← IntegrableOn]
--     apply hg_integ.mono _ le_rfl
--     refine Set.Ioi_subset_Ioi hx.le
--   · exact measurableSet_Ioi
--   · simp only [Set.mem_Ioi]
--     intro y hy
--     convert hC _ (by linarith) using 2
--     rw [abs_of_nonneg (hg _)]


-- example {ι : Type*} {f g : ℝ → ℝ} (s : ι → Set ℝ) (l : Filter ℝ) (l' : Filter ι)
--     (hl : ∀ i, ∀ᶠ x in l, x ∈ s i)
--     (hf : Measurable f)
--     (hg : g =O[l] (fun _ ↦ (1:ℝ))) :
--     (fun i ↦ ∫ x in (s i), f x * g x) =O[l'] (fun i ↦ ∫ x in (s i), f x) := by
--   rw [isBigO_iff] at hg
--   obtain ⟨C, hC⟩ := hg
--   rw [isBigO_iff]; use C
--   filter_upwards with i
--   simp only [norm_eq_abs]
--   simp only [eventually_mem_set] at hl
--   sorry


theorem integral_mul_E₁_tail_isBigO (a : ℝ) (ha : 1 < a) :
    (fun x ↦ ∫ (t : ℝ) in Set.Ioi x, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t)
    =O[𝓟 (Set.Ioi a)] (fun x ↦ (Real.log x)⁻¹) := by
  obtain ⟨C, hC_pos, hC⟩ := (E₁_isBigO_one ha).exists_pos
  rw [isBigO_iff]
  use C
  simp only [isBigOWith_principal, Set.mem_Ici, norm_eq_abs, norm_one, mul_one] at hC
  simp only [norm_eq_abs, norm_inv, eventually_principal, Set.mem_Ioi]
  intro x hx
  calc
    _ ≤ ∫ t in Set.Ioi x, |t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t| := by
      apply abs_integral_le_integral_abs
    _ = ∫ t in Set.Ioi x, t⁻¹ * (Real.log t)⁻¹ ^ 2 * |E₁ t| := by
      apply setIntegral_congr_fun
      · exact measurableSet_Ioi
      intro t ht
      simp only [Set.mem_Ioi] at ht
      simp_rw [abs_mul, abs_pow]
      rw [abs_of_nonneg, abs_of_nonneg]
      · bound
      · bound
    _ ≤ C * ∫ t in Set.Ioi x, t⁻¹ * (Real.log t)⁻¹ ^ 2 := by
      simp_rw [← smul_eq_mul, ← integral_smul, smul_eq_mul]
      apply setIntegral_mono_on_fun_of_nonneg
      · apply Measurable.aestronglyMeasurable
        fun_prop
      · rw [IntegrableOn]
        apply Integrable.const_mul
        rw [← IntegrableOn]
        apply (integrable_inv_mul_log_inv_sq x (ha.trans hx)).mono _ le_rfl
        exact Set.Ioi_subset_Ici_self
      · exact measurableSet_Ioi
      · intro t ht
        simp only [Set.mem_Ioi] at ht
        rw [mul_comm C]
        gcongr
        · bound
        · apply hC _ (hx.trans ht).le
      · simp only [Set.mem_Ioi, inv_pow]
        bound
    _ = _ := by
      rw [abs_of_nonneg, setIntegral_Ioi_inv_mul_inv_log_sq ]
      · exact ha.trans hx
      · bound
        -- apply Real.log_nonneg (by linarith)

-- This was a pain point: I want uniform bounds to show integrability of E₁, since E₁ is definitely not continuous
-- Perhaps one could argue, E₁ is a step function plus a

theorem integrable_mul_E₁ (a b : ℝ) (ha : 1 < a) :
  MeasureTheory.Integrable (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2 * E₁ a)
    (MeasureTheory.volume.restrict (Set.Icc a b)) := by
  rw [← IntegrableOn]
  apply (integrableOn_Ici_fun_mul_E₁ a (by linarith)).mono Set.Icc_subset_Ici_self le_rfl


noncomputable def mertens₂Const : ℝ := (∫ (t : ℝ) in Set.Ioi 2, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t)
  - Real.log (Real.log 2) + 1

theorem mertens₂Const_eq (a : ℝ) (ha : 1 < a) (ha' : a ≤ 2) :
  mertens₂Const = (∫ (t : ℝ) in Set.Ioi a, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t)
  - Real.log (Real.log a) + 1 := by
  have h₀ : ∫ (t : ℝ) in Set.Ioi a, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t =
    (∫ (t : ℝ) in Set.Ioc a 2, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) +
      ∫ (t : ℝ) in Set.Ioi 2, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t := by
    rw [← setIntegral_union]
    · rw [Set.Ioc_union_Ioi_eq_Ioi ha']
    · exact Set.Ioc_disjoint_Ioi_same
    · exact measurableSet_Ioi
    · apply (integrableOn_Ici_fun_mul_E₁ a ha).mono _ le_rfl
      intro x
      simp +contextual only [Set.mem_Ioc, Set.mem_Ici, LT.lt.le, implies_true]
    · apply (integrableOn_Ici_fun_mul_E₁ a ha).mono _ le_rfl
      intro x
      simp only [Set.mem_Ioi, Set.mem_Ici]
      intro hx
      apply (ha'.trans hx.le)
  have h₁ := calc
    ∫ (t : ℝ) in Set.Ioc a 2, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t =
      - ∫ (t : ℝ) in Set.Ioc a 2, t⁻¹ * (Real.log t)⁻¹ := by
      rw [← integral_neg]
      simp_rw [integral_Ioc_eq_integral_Ioo]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (by measurability)] with t ht
      simp only [Set.mem_Ioo] at ht
      rw [E₁_of_lt_two t (by linarith) ht.2]
      have : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne.symm
      have : t ≠ 0 := by linarith
      field_simp
    _ = Real.log (Real.log a) - Real.log (Real.log 2) := by
      rw [integral_inv_mul_invlog a 2 ha ha']
      ring
  rw [h₀, h₁, mertens₂Const]
  ring

/-
Notable pain points: positivity / nonnegativity and log, proving Real.log x ≠ 0 is annoying. Automation
like `positivity` and `field_simp` can't work with this very well.
-/
-- TODO : replace 1 / p with p⁻¹
theorem mertens_second (a : ℝ) (ha : 1 < a) (ha' : a < 2)
: (fun t : ℝ ↦ (∑ p ∈ primesBelow (⌊t⌋₊+1), (p : ℝ)⁻¹) - (Real.log (Real.log t) + mertens₂Const))
    =O[𝓟 (Set.Ioi a)] (fun n ↦ (Real.log n)⁻¹) := by
  have ha_pos : 0 < a := by linarith
  let ϕ (x : ℝ) : ℝ := (Real.log x)⁻¹
  let c (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0
  have h' (b : ℝ) : ContinuousOn (fun x:ℝ ↦ - x⁻¹ * (Real.log x)⁻¹^2) (Set.Icc a b) := by
    intro x
    simp only [Set.mem_Icc, inv_pow, neg_mul, and_imp]
    intro hx _
    apply ContinuousAt.continuousWithinAt
    have : x ≠ 0 := by linarith
    apply (continuousAt_inv₀ this).mul ((continuousAt_inv₀ _).comp
      ((continuousAt_id.log this).pow 2)) |>.neg
    simp only [id_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, log_eq_zero,
      not_or]
    refine ⟨this, ?_, ?_⟩ <;> linarith
  have hϕ := hasDerivAt_log_inv
  have hfloor : ⌊(a : ℝ)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    norm_num
    constructor <;> linarith
  have (b : ℝ) (hb : a ≤ b) :
      ∑ k ∈ Finset.Ioc 1 ⌊b⌋₊, ϕ k * c k = ϕ b * ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k - ϕ a * 0 -
        ∫ t in Set.Ioc a b, - t⁻¹ * (Real.log t)⁻¹ ^ 2 * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
    convert sum_mul_eq_sub_sub_integral_mul''  c (fun x ↦ - x⁻¹ * (Real.log x)⁻¹ ^ 2) ?_ hb ?_ ?_
    · rw [hfloor]
    · apply (sum_eq_zero ..).symm
      simp only [hfloor, mem_Icc, _root_.zero_le, true_and, ite_eq_right_iff, div_eq_zero_iff,
        log_eq_zero, cast_eq_zero, cast_eq_one, c]
      omega
    · exact ha_pos.le
    · simp only [Set.mem_Icc, and_imp]
      intro t ht _
      exact (hϕ t (by linarith))
    · apply MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact
      · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
        continuity
      · exact isCompact_Icc
  simp only [mul_zero, sub_zero, ϕ, c, ← sum_filter, Icc_filter_prime, E₁_eq_add] at this

  have eqn (t : ℝ) (ht : a ≤ t) :=
    have hlogt : Real.log t ≠ 0 := (Real.log_pos (ha.trans_le ht)).ne.symm
    calc
      ∑ p ∈ (⌊t⌋₊ + 1).primesBelow, (p:ℝ)⁻¹ =
        (∑ x ∈ Ioc 1 ⌊t⌋₊, (Real.log ↑x)⁻¹ * if Nat.Prime x then Real.log ↑x / ↑x else 0) := by
        simp_rw [mul_ite, mul_zero, ← sum_filter]
        apply sum_congr
        · ext p
          simp only [mem_primesBelow, mem_filter, mem_Ioc, and_congr_left_iff]
          intro hp
          refine ⟨fun hpt ↦ ⟨hp.one_lt, (by omega)⟩, fun ⟨_, hpt⟩ ↦ (by omega)⟩
        simp only [mem_filter, mem_Ioc, and_imp]
        intro x hx _ _
        rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀, one_mul]
        apply (Real.log_pos (mod_cast hx)).ne.symm
      _ =
      (1 + (Real.log t)⁻¹ * E₁ t) -
          ∫ (t : ℝ) in Set.Ioc a t, - t⁻¹ * (Real.log t)⁻¹ ^ 2  * (Real.log t + E₁ t) := by
        convert this t ht using 2
        rw [mul_add, inv_mul_cancel₀ hlogt]
      _ =
      (1 + (Real.log t)⁻¹ * E₁ t) +
          (∫ (t : ℝ) in Set.Icc a t, t⁻¹ * (Real.log t)⁻¹ + t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) := by
        simp_rw [← MeasureTheory.integral_Icc_eq_integral_Ioc, neg_mul, MeasureTheory.integral_neg,
          sub_neg_eq_add, mul_add]
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)]
        intro x
        simp only [Set.mem_Icc, add_left_inj, and_imp]
        intro hx _
        have := (Real.log_pos (by linarith)).ne.symm
        field_simp [show x ≠ 0 by linarith]
      _ =
      (1 + (Real.log t)⁻¹ * E₁ t) +
          ((∫ (t : ℝ) in Set.Icc a t, t⁻¹ * (Real.log t)⁻¹) +
            ∫ (t : ℝ) in Set.Icc a t, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) := by
        rw [MeasureTheory.integral_add (integrable_inv_mul_log_inv_Icc _ _ (by linarith))
          (integrable_mul_E₁ _ _ (by linarith))]
      _ =
          Real.log (Real.log t) + mertens₂Const + (Real.log t)⁻¹ * E₁ t -
            ∫ (t : ℝ) in Set.Ioi t, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t := by
        rw [mertens₂Const_eq a ha ha'.le, integral_Icc_eq_integral_Ioc,
          integral_inv_mul_invlog _ _ ha ht, integral_mul_E₁_eq_const_sub_integral _ _ ha ht]
        ring

  apply Asymptotics.IsBigO.congr'  (f₁ := fun t ↦ (Real.log t)⁻¹ * E₁ t -
    ∫ (t : ℝ) in Set.Ioi t, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) (g₁ := fun t ↦ (Real.log t)⁻¹)
      (g₂ := fun t ↦ (Real.log t)⁻¹)
  · apply Asymptotics.IsBigO.sub
    · apply (Asymptotics.isBigO_refl (fun t ↦ (Real.log t)⁻¹) _).mul (E₁_isBigO_one ha) |>.mono _
        |>.congr_right
      · simp only [mul_one, implies_true]
      · simp only [le_principal_iff, mem_principal, Set.Ioi_subset_Ici_iff, le_refl]
    · exact integral_mul_E₁_tail_isBigO a ha
  · simp only [eventuallyEq_principal]
    intro t ht
    simp only [Set.mem_Ioi] at ht
    simp only
    rw [eqn t ht.le]
    ring
  · exact fun ⦃a_1⦄ ↦ congrFun rfl

end MertensSecond

section MertensThird

theorem hasSum_pow_div_add_two {x : ℝ} (hx : |x| < 1) : HasSum (fun n : ℕ ↦ x ^ (n+2) / (n+2))
    (-Real.log (1-x) - x) := by
  norm_cast
  erw [hasSum_nat_add_iff (f := fun n ↦ x ^ (n+1) / ↑(n+1)) 1]
  simp only [cast_add, cast_one, range_one, sum_singleton, zero_add, pow_one, CharP.cast_eq_zero,
    div_one]
  convert Real.hasSum_pow_div_log_of_abs_lt_one hx using 1
  ring

theorem sum_inv_sub_sum_log (n : ℕ)  :
  ∑ p ∈ primesBelow (n+1), -Real.log (1 - (p:ℝ)⁻¹) - ∑ p ∈ primesBelow (n + 1), (p:ℝ)⁻¹ =
    ∑ p ∈ primesBelow (n+1), ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2)  := by
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  simp only [mem_primesBelow] at hp
  rw [(hasSum_pow_div_add_two _).tsum_eq]
  rw [abs_inv, inv_lt_one_iff₀]
  simp only [abs_cast, cast_nonpos, one_lt_cast, hp.2.one_lt, or_true]


variable {ι : Type*}
  {f g : ι → ℝ} in
theorem tsum_le_tsum_of_nonneg (h : ∀ i, f i ≤ g i) (hf : ∀ x, 0 ≤ f x) (hg : Summable g) :
    ∑' i, f i ≤ ∑' i, g i := by
  apply Summable.tsum_le_tsum h _ hg
  apply hg.of_nonneg_of_le hf h

theorem tsum_inv_pow_div_id_le (x : ℝ) (hx : 1 < x)  :
  ∑' n : ℕ, x⁻¹^(n+2) / (n+2) ≤ (x * (x-1):ℝ)⁻¹ :=
  have geom : HasSum (fun n : ℕ ↦ x⁻¹ ^ n) ((1 - x⁻¹)⁻¹) := by
    apply hasSum_geometric_of_abs_lt_one
    rw [abs_inv, inv_lt_one_iff₀]
    simp [hx, lt_abs]
  have summable : Summable fun i ↦ x⁻¹ ^ (i + 2) := by
    rw [summable_nat_add_iff]
    exact geom.summable
  calc
  _ ≤ ∑' n : ℕ, x⁻¹^(n+2) := by
    apply tsum_le_tsum_of_nonneg
    · intro n
      apply _root_.div_le_self
      · positivity
      · norm_cast
        omega
    · bound
    · apply summable
  _ = (x * (x - 1):ℝ)⁻¹  := by
    have : HasSum (fun n : ℕ ↦ x⁻¹^(n+2)) ((1-x⁻¹)⁻¹*x⁻¹^2) := by
      simp_rw [pow_add, ]
      rw [hasSum_mul_right_iff (by positivity)]
      · exact geom
    convert this.tsum_eq using 1
    rw [inv_pow, ← mul_inv]
    congr 1
    field [show x ≠ 0 by positivity]

theorem tsum_inv_pow_div_id_le_nat (p : ℕ) (hp : 1 < p)  :
  ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) ≤ (p * (p-1):ℝ)⁻¹ :=
  tsum_inv_pow_div_id_le p (mod_cast hp)

theorem summable_aux :
    Summable (fun n : ℕ ↦ (n * (n-1):ℝ)⁻¹) := by
  apply summable_of_isBigO_nat (g := fun n:ℕ ↦ n ^ (-2:ℝ))
  · simp only [summable_nat_rpow, neg_lt_neg_iff, one_lt_ofNat]
  apply mul_sub_one_inv_isBigO_neg_two.comp_tendsto tendsto_natCast_atTop_atTop

theorem summable_thing :
  Summable (fun p : ℕ ↦ ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2)) := by
  apply Summable.of_norm_bounded_eventually_nat summable_aux
  filter_upwards [eventually_gt_atTop 1] with p hp
  rw [norm_eq_abs, abs_of_nonneg]
  · exact tsum_inv_pow_div_id_le p (mod_cast hp)
  · bound

theorem summable_thing' :
  Summable (fun p : ℕ ↦ if p.Prime then ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) else 0) := by
  simp_rw (singlePass := true)[← Set.mem_setOf (p := Nat.Prime), ← Set.indicator_apply
    {n : ℕ | n.Prime} (fun p ↦ ∑' (n : ℕ), (↑p:ℝ)⁻¹ ^ (n + 2) / (↑n + 2))]
  apply Summable.indicator
  exact summable_thing

theorem sum_primesBelow_tsum_eq_tsum_sub_tsum (k : ℕ):
    ∑ p ∈ primesBelow (k+1), ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) =
      (∑' p : ℕ, if p.Prime then ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) else 0)
      - (∑' p : ℕ, if (p + k + 1).Prime then ∑' n : ℕ, (↑(p+k+1):ℝ)⁻¹^(n+2) / (n+2) else 0) := by
  rw [Nat.primesBelow, sum_filter, eq_sub_iff_add_eq]
  apply Summable.sum_add_tsum_nat_add (k := k+1)
    (f := fun p ↦ if p.Prime then ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) else 0)
  convert summable_thing' with p

theorem telescoping_series (f : ℕ → ℝ) (hf : Antitone f) (htends : Tendsto f atTop (nhds 0)) :
    ∑' n, (f n - f (n + 1)) = f 0 := by
  have (n : ℕ): ∑ i ∈ Finset.range n, (f i - f (i+1)) = f 0 - f n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      ring
  have : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (f i - f (i+1))) atTop (nhds (f 0)) := by
    simp_rw [this]
    convert tendsto_const_nhds.sub htends
    ring
  apply tendsto_nhds_unique (Summable.tendsto_sum_tsum_nat ?_) this
  rw [summable_iff_not_tendsto_nat_atTop_of_nonneg]
  · exact not_tendsto_atTop_of_tendsto_nhds this
  intro n
  linarith [hf (le_succ n)]

theorem tsum_mul_succ_inv (k : ℕ) (hk : 0 < k) :
    (∑' n : ℕ, (↑(n+k+1) * (↑(n+k+1)-1) : ℝ)⁻¹) = (k:ℝ)⁻¹  := by
  let f (n : ℕ) := (↑(n + k):ℝ)⁻¹
  have (n : ℕ) : f n - f (n+1) = (↑(n+k+1) * (↑(n+k+1)-1) : ℝ)⁻¹ := by
    simp only [f]
    push_cast
    ring_nf
    field
  simp_rw [← this]
  convert telescoping_series f ?_ ?_
  · ring
  · simp only [f]
    intro a b hab
    simp only [cast_add]
    gcongr
  · simp only [f]
    apply tendsto_inv_atTop_zero.comp
    apply tendsto_natCast_atTop_atTop.comp
    exact tendsto_add_atTop_nat k

private theorem tailSum_isBigO_inv_nat :
    (fun k ↦ ∑' p : ℕ, if (p + k + 1).Prime then ∑' n : ℕ, (↑(p+k+1):ℝ)⁻¹^(n+2) / (n+2) else 0)
    =O[atTop] fun n : ℕ ↦ (n:ℝ)⁻¹ := by
  calc
    _ =O[atTop] fun k : ℕ ↦ (∑' p : ℕ, (↑(p + k + 1) * (↑(p + k + 1) - 1))⁻¹ : ℝ) := by
      apply Filter.Eventually.isBigO
      filter_upwards [eventually_gt_atTop 1] with k hk
      rw [norm_eq_abs, abs_of_nonneg ?nonneg]
      case nonneg =>
        bound
      apply tsum_le_tsum_of_nonneg
      · bound [tsum_inv_pow_div_id_le_nat]
      · bound
      · apply (summable_nat_add_iff (k+1)).mpr summable_aux
    _ =ᶠ[atTop] _ := by
      filter_upwards [eventually_gt_atTop 0] with k hk
      apply tsum_mul_succ_inv k hk

private theorem tailSum_isBigO_inv_nat_Ici :
    (fun k ↦ ∑' p : ℕ, if (p + k + 1).Prime then ∑' n : ℕ, (↑(p+k+1):ℝ)⁻¹^(n+2) / (n+2) else 0)
    =O[𝓟 <| Set.Ici 1] fun n : ℕ ↦ (n:ℝ)⁻¹ := by
  apply isBigO_nat_of_isBigO_atTop tailSum_isBigO_inv_nat
  simp only [inv_eq_zero, cast_eq_zero, cast_add, cast_one, inv_pow, eventually_principal,
    Set.mem_Ici]
  intros
  omega

theorem tendsto_floor_Ici_Ici (n : ℕ) :
    Tendsto (Nat.floor : ℝ → ℕ) (𝓟 <| Set.Ici n) (𝓟 <| Set.Ici n) := by
  simp +contextual [Nat.le_floor]

private theorem tailSum_isBigO_inv :
    (fun x:ℝ ↦ ∑' p : ℕ, if (p + ⌊x⌋₊ + 1).Prime then
      ∑' n : ℕ, (↑(p+⌊x⌋₊+1):ℝ)⁻¹^(n+2) / (n+2) else 0)
    =O[𝓟 <| Set.Ici 1] fun x : ℝ ↦ (⌊x⌋₊:ℝ)⁻¹ := by
  apply tailSum_isBigO_inv_nat_Ici.comp_tendsto (mod_cast (tendsto_floor_Ici_Ici 1))

theorem le_two_mul_floor (x : ℝ) : x / ↑⌊x⌋₊ ≤ 2 := by
  by_cases hx' : x < 1
  · rw [Nat.floor_eq_zero.mpr hx']
    · simp
  rw [div_le_iff₀ (by bound)]
  by_cases h : 2 ≤ x
  · bound [Nat.lt_floor_add_one x]
  · have : ⌊x⌋₊ = 1 := by
      rw [Nat.floor_eq_iff]
      · constructor <;> norm_num <;> linarith
      · linarith
    simp only [this, cast_one, mul_one, ge_iff_le]
    linarith

theorem floor_inv_isBigO_inv : (fun x : ℝ ↦ (⌊x⌋₊ : ℝ)⁻¹) =O[⊤] (fun x : ℝ ↦ x⁻¹) := by
  rw [Asymptotics.isBigO_iff]
  use 2
  simp only [norm_inv, RCLike.norm_natCast, norm_eq_abs, eventually_top]
  intro x
  by_cases hx' : x < 1
  · rw [Nat.floor_eq_zero.mpr hx']
    · simp
  rw [abs_of_nonneg (by linarith), le_mul_inv_iff₀ (by linarith), mul_comm,
    ← div_eq_mul_inv]
  exact le_two_mul_floor x

theorem mertens3_sub_mertens2_isBigO (a : ℝ) (ha : 1 < a) :
    (fun x ↦ (∑ p ∈ primesBelow (⌊x⌋₊ + 1), -Real.log (1 - (p:ℝ)⁻¹)
    - ∑ p ∈ primesBelow (⌊x⌋₊ + 1), (p:ℝ)⁻¹)
    - (∑' p : ℕ, if p.Prime then ∑' n : ℕ, (↑(p):ℝ)⁻¹^(n+2) / (n+2) else 0))
    =O[𝓟 <| Set.Ioi a]  (fun x ↦ x⁻¹) := by
  simp_rw [sum_inv_sub_sum_log, sum_primesBelow_tsum_eq_tsum_sub_tsum]
  apply (tailSum_isBigO_inv.neg_left.mono _).trans (floor_inv_isBigO_inv.mono le_top) |>.congr'
  · filter_upwards with x
    ring
  · rfl
  · simp [ha.le]

noncomputable def M : ℝ := (∑' p : ℕ, if p.Prime then ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) else 0)

noncomputable def mertens₃Const : ℝ :=
  M + mertens₂Const

theorem inv_isBigO_inv_log_Ioi (a : ℝ) (ha : 1 < a) :
  (fun x : ℝ ↦ x⁻¹) =O[𝓟 (Set.Ioi a)] (fun x : ℝ ↦ (Real.log x)⁻¹) := by
  rw [isBigO_iff]
  use 1
  simp only [norm_inv, norm_eq_abs, one_mul, eventually_principal, Set.mem_Ioi]
  intro x hx
  have hxpos : 0 < x := by linarith
  rw [abs_of_nonneg hxpos.le, abs_of_nonneg (Real.log_nonneg (ha.trans hx).le), inv_le_inv₀]
  · apply Real.log_le_self hxpos.le
  · linarith
  · apply Real.log_pos (ha.trans hx)

theorem mertens_third_log_aux (a : ℝ) (ha : 1 < a) (ha' : a < 2) :
    (fun x : ℝ ↦ ∑ p ∈ primesBelow (⌊x⌋₊ + 1), -Real.log (1 - (p:ℝ)⁻¹) -
      (Real.log (Real.log x) + mertens₃Const))
      =O[𝓟 (Set.Ioi a)] (fun x ↦ (Real.log x)⁻¹) := by
  have h₀ := mertens3_sub_mertens2_isBigO a ha |>.trans <| inv_isBigO_inv_log_Ioi a ha
  have h₁ := mertens_second a ha ha'
  simp_rw [sub_sub] at h₀
  rw [mertens₃Const, M]
  apply (h₀.add h₁).congr
  · intro x
    ring
  · intro
    rfl

theorem mertens_third_log (a : ℝ) (ha : 1 < a) (ha' : a < 2):
  (fun x : ℝ ↦ ∑ p ∈ primesBelow (⌊x⌋₊ + 1), Real.log (1 - (p:ℝ)⁻¹) -
    (-Real.log (Real.log x) - mertens₃Const))
    =O[𝓟 (Set.Ioi a)] (fun x ↦ (Real.log x)⁻¹) := by
  convert (mertens_third_log_aux a ha ha').neg_left using 2 with x
  simp only [sum_neg_distrib, neg_sub, sub_neg_eq_add]
  ring

theorem mertens_third_log_isLittleO_one :
  (fun x : ℝ ↦ ∑ p ∈ primesBelow (⌊x⌋₊ + 1), Real.log (1 - (p:ℝ)⁻¹) -
  (-Real.log (Real.log x) - mertens₃Const))
    =o[atTop] (fun _ ↦ (1:ℝ)) := by
  have h₀ : (fun x ↦ (Real.log x)⁻¹) =o[atTop] (fun x ↦ (1:ℝ)) := by
    simp_rw [Asymptotics.isLittleO_one_iff]
    apply tendsto_inv_atTop_zero.comp  tendsto_log_atTop
  apply (mertens_third_log (3/2) (by norm_num) (by norm_num)).mono ?_ |>.trans_isLittleO h₀
  intro s hs
  have := Filter.Ioi_mem_atTop (3/2:ℝ)
  apply Filter.mem_of_superset this
  simpa [this]

theorem sum_primesBelow_log_eq {n : ℕ} : ∑ p ∈ primesBelow n, Real.log (1 - (p:ℝ)⁻¹) =
    Real.log (∏ p ∈ primesBelow n, (1 - (p : ℝ)⁻¹)) := by
  rw [Real.log_prod]
  intro p hp
  rw [mem_primesBelow] at hp
  have : 1 < (p:ℝ) := mod_cast hp.2.one_lt
  apply _root_.ne_of_gt
  bound

theorem mertens_third :
    IsEquivalent atTop (fun x ↦ ∏ p ∈ primesBelow (⌊x⌋₊ + 1), (1 - (p : ℝ)⁻¹))
      (fun x ↦ exp (- mertens₃Const) * (Real.log x)⁻¹) := by
  apply mertens_third_log_isLittleO_one.isEquivalent_exp.congr_left _ |>.congr_right
  · filter_upwards [eventually_gt_atTop 100] with x hx
    rw [Real.exp_sub, Real.exp_neg, Real.exp_neg, Real.exp_log]
    · ring
    bound
  · filter_upwards with x
    simp_rw [sum_primesBelow_log_eq]
    rw [Real.exp_log]
    apply Finset.prod_pos
    intro p hp
    rw [mem_primesBelow] at hp
    have : 1 < (p:ℝ) := mod_cast hp.2.one_lt
    bound



end MertensThird
