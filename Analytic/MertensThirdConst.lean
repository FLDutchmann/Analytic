import Analytic.Mertens


open Filter Asymptotics Real Topology

open scoped Filter

noncomputable def zeta (x : ℝ) : ℝ := (riemannZeta x).re


theorem Complex.im_tsum_eq_zero {ι : Type*} {f : ι → ℂ} (hf : ∑' n, (f n).im = 0) :
    (∑' n, f n).im = 0 := by
  by_cases hf' : Summable f
  · rw [Complex.im_tsum hf', hf]
  · simp [tsum_eq_zero_of_not_summable hf']

theorem im_riemannZeta_eq_zero (x : ℝ) (hx : 1 < x) : (riemannZeta x).im = 0 := by
  rw [zeta_eq_tsum_one_div_nat_cpow]
  · apply Complex.im_tsum_eq_zero
    convert tsum_zero with n
    · simp only [one_div, Complex.inv_im, div_eq_zero_iff, neg_eq_zero, map_eq_zero,
      Complex.cpow_eq_zero_iff, Nat.cast_eq_zero, ne_eq, Complex.ofReal_eq_zero]

      rw [show (n : ℂ) = (n : ℝ) by simp, ← Complex.ofReal_cpow]
      simp only [Complex.ofReal_im, true_or]
      norm_cast
      simp only [zero_le]
  exact_mod_cast hx

-- theorem riemannZeta_ofReal (x : ℝ) : riemannZeta x = zeta x := by
--   sorry
-- theorem riemannZeta_ofReal' (x : ℝ) (hx : 1 < x) : riemannZeta x = zeta x := by
--   sorry
theorem zeta_ne_zero (x : ℝ) (hx : 1 < x) : zeta x ≠ 0 := by
  have := riemannZeta_ne_zero_of_one_lt_re (s := x) (by simp [hx])
  rw [← Complex.re_add_im (riemannZeta x), im_riemannZeta_eq_zero x hx] at this
  simpa only [Complex.ofReal_zero, zero_mul, add_zero, ne_eq, Complex.ofReal_eq_zero] using this

-- theorem test (f : ℕ → ℂ) (hf : ∀ n, (f n).im = 0) :

theorem Complex.hasProd_iff_ofReal {ι : Type*} {f : ι → ℝ} {a : ℝ} :
    HasProd f a ↔ HasProd (fun x ↦ (f x : ℂ)) a := by
  simp_rw [HasProd]
  constructor
  · intro h
    have := Complex.continuous_ofReal.continuousAt.tendsto.comp h
    simp only [Function.comp_def, Complex.ofReal_prod] at this
    convert this
  · intro h
    have := Complex.continuous_re.continuousAt.tendsto.comp h
    simpa only [← Complex.ofReal_prod, Function.comp_def, Complex.ofReal_re] using this

theorem Complex.tprod_ofReal {ι : Type*} (f : ι → ℝ) : ∏' n, (f n : ℂ) = ↑(∏' n, f n) := by
  by_cases h : Multipliable f
  · apply Complex.hasProd_iff_ofReal.mp h.hasProd |>.tprod_eq
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

theorem Complex.multipliable_iff_ofReal {ι : Type*} {f : ι → ℝ} :
    Multipliable f ↔ Multipliable (fun x ↦ (f x : ℂ)) := by
  rw [Multipliable ]
  simp_rw [Complex.hasProd_iff_ofReal]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    use ∏' n, f n
    rw [← Complex.tprod_ofReal]
    apply ha.multipliable.hasProd

/- Surely there is a better way to do this?? -/

theorem hassum_log {ι : Type*} {f : ι → ℝ} {a : ℝ} (ha : a ≠ 0) (h : HasProd f a) :
    HasSum (fun x ↦ Real.log (f x)) (Real.log a) := by
  have hf : ∀ i, f i ≠ 0 := by
    intro i hi
    apply ha (h.unique <| hasProd_zero_of_exists_eq_zero ⟨i, hi⟩)
  rw [HasProd] at h
  have := (Real.continuousAt_log ha).tendsto.comp h
  simp only [Function.comp_def] at this
  rw [HasSum]
  convert this
  rw [log_prod]
  intro x _
  exact hf x

theorem Real.multipliable_zeta (x : ℝ) (hx : 1 < x) :
    Multipliable (fun p : Nat.Primes ↦ (1 - (p:ℝ)^(-x))⁻¹) := by
  have hprod := riemannZeta_eulerProduct_hasProd (s := x) (by simp [hx]) |>.multipliable
  have : (fun p : Nat.Primes ↦ (1 - ↑↑p ^ (-↑x:ℂ):ℂ)⁻¹) =
      fun p : Nat.Primes ↦ (↑(1 - p ^ (-x:ℝ) : ℝ)⁻¹ : ℂ) := by
    ext p
    simp only [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, inv_inj, sub_right_inj]
    rw [Complex.ofReal_cpow] <;> simp
  simp only [this, ←Complex.multipliable_iff_ofReal, Nat.cast_nonneg] at hprod
  apply hprod

theorem Real.zeta_eulerProd (x : ℝ) (hx : 1 < x) :
    zeta x = ∏' p : Nat.Primes, (1 - (p:ℝ)^(-x))⁻¹ := by
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
    simp only [Complex.ofReal_re]

theorem Real.hasProd_zeta (x : ℝ) (hx : 1 < x) :
    HasProd (fun p : Nat.Primes ↦ (1 - (p:ℝ)^(-x))⁻¹) (zeta x) := by
  rw [Real.multipliable_zeta x hx |>.hasProd_iff]
  apply Real.zeta_eulerProd x hx |>.symm

theorem Asymptotics.IsBigO.re {α F : Type*} [Norm F] {l : Filter α} {f : α → ℂ} {g : α → F}
    (h : f =O[l] g) : (Complex.re ∘ f) =O[l] g := by
  apply IsBigO.trans _ h
  apply IsBigO.of_norm_right
  apply IsBigO.of_norm_le
  intro x
  simp only [Function.comp_apply, norm_eq_abs]
  exact Complex.abs_re_le_norm (f x)

/- This is actually true for `𝓝 0`, but we only need it to the right of 0.-/
theorem zeta_pole_estimate_nhdsWithin :
    (fun σ:ℝ ↦ zeta (1+σ) - σ⁻¹) =O[𝓝[>] 0] (fun _ ↦ (1:ℝ)) := by
  have : (fun σ:ℂ ↦ riemannZeta (1+σ) - σ⁻¹) =O[𝓝 0] (fun _ ↦ (1:ℝ)) := by
    have := (isBigO_riemannZeta_sub_one_div (F := ℝ))
    have := this.comp_tendsto (add_zero (1:ℂ) ▸ (continuous_add_left (1:ℂ)).tendsto 0)
    simpa only [one_div, Function.comp_def, add_sub_cancel_left] using this
  have := this.comp_tendsto (Complex.continuous_ofReal.tendsto _)
  simp only [one_div, Function.comp_def] at this
  apply (this.re.mono nhdsWithin_le_nhds).congr'
  · filter_upwards with σ
    simp only [Function.comp_apply, Complex.sub_re, Complex.inv_re, Complex.ofReal_re,
      Complex.normSq_ofReal, div_self_mul_self', sub_left_inj, zeta]
    norm_num
  · rfl

theorem euler_product {σ : ℝ} (hσ : 0 < σ) :
    zeta (1+σ) = ∏' p : Nat.Primes, (1 - ((p:ℝ)^(-(1+σ))))⁻¹ := by
  apply Real.zeta_eulerProd (1 + σ)
  linarith

theorem hasSum_log_zeta {σ : ℝ} (hσ : 0 < σ) :
     HasSum (fun p : Nat.Primes ↦ log ((1 - (p:ℝ)^(-(1+σ)))⁻¹)) (log (zeta (1+σ))) := by
  apply hassum_log (zeta_ne_zero _ (by linarith))
  apply Real.hasProd_zeta _ (by linarith)


theorem Real.log_zeta {σ : ℝ} (hσ : 0 < σ) :
    log (zeta (1+σ)) = ∑' p : Nat.Primes, log ((1 - (p:ℝ)^(-(1+σ)))⁻¹) := by
  rw [hasSum_log_zeta hσ |>.tsum_eq]

private noncomputable def f (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (log ((1 - (p:ℝ)^(-(1+σ)))⁻¹) - (p : ℝ)^(-(1+σ)))

theorem f_def' {σ : ℝ} (hσ : 0 < σ) : f σ = log (zeta (1+σ)) - ∑' (p : Nat.Primes), (p:ℝ) ^ (-(1+σ)) := by
  rw [f, tsum_sub, Real.log_zeta hσ]
  · apply hasSum_log_zeta hσ |>.summable
  · have := Real.summable_nat_rpow (p := -(1 + σ)) |>.mpr (by linarith)
    apply this.subtype Nat.Prime

theorem f_term_eq_tsum (x : ℝ) (hx : |x| < 1) :
    log (1 - x)⁻¹ - x = ∑' n : ℕ, x^(n+2)/(n+2)  := by
  rw [Real.log_inv, hasSum_pow_div_add_two hx |>.tsum_eq]

theorem f_term_eq_tsum' (p : Nat.Primes) {σ : ℝ} (hσ : 0 ≤ σ) :
    log (1 - p ^ (-(1+σ)))⁻¹ - p ^ (-(1+σ)) = ∑' n : ℕ, (p ^ (-(1+σ)):ℝ)^(n+2)/(n+2)  := by
  apply f_term_eq_tsum
  rw [rpow_neg (by norm_num), abs_inv, ]
  apply inv_lt_one_of_one_lt₀
  rw [lt_abs]
  left
  apply lt_of_lt_of_le (b := (p ^ (1:ℝ):ℝ))
  · simp [p.2.one_lt]
  apply Real.rpow_le_rpow_of_exponent_le
  · simp [p.2.one_le]
  · linarith

theorem f_term_mono (p : Nat.Primes) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑' n : ℕ, (p ^ (-(1+σ)):ℝ)^(n+2)/(n+2) ≤ ∑' n : ℕ, ((p⁻¹):ℝ)^(n+2)/(n+2) := by
  rw [rpow_neg]
  apply tsum_le_tsum_of_nonneg
  · intro n
    gcongr
    · simp [p.2.pos]
    · trans (p:ℝ)^(1:ℝ)
      · simp
      · apply Real.rpow_le_rpow_of_exponent_le
        · simp [p.2.one_le]
        linarith only [hσ]
  · intro x
    positivity
  · apply (hasSum_pow_div_add_two ..).summable
    rw [abs_inv]
    apply inv_lt_one_of_one_lt₀
    simp [p.2.one_lt]
  · positivity

theorem f_eq_tsum_tsum (σ : ℝ) (hσ : 0 ≤ σ) :
    f σ =  ∑' p : Nat.Primes, ∑' n : ℕ, ((p:ℝ)^(-(1+σ)))^(n+2)/(n+2) := by
  apply tsum_congr
  intro p
  rw [f_term_eq_tsum' p hσ]


theorem f_continuousOn : ContinuousOn f (Set.Ici 0) := by
  have hcont {p : Nat.Primes} : Continuous fun x : ℝ  ↦ (p:ℝ) ^ (-(1 + x)) := by
    apply Real.continuous_const_rpow (by simp [p.2.ne_zero])|>.comp
    fun_prop
  have mt {p : Nat.Primes} {σ : ℝ} (hσ : 0 ≤ σ) : ¬ 1 - (p : ℝ)^(-σ - 1) = 0 := by
    suffices (p : ℝ)^(-σ - 1) ≠ 1 by
      linarith +splitNe only [this]
    apply ne_of_lt
    apply rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast p.2.one_lt
    linarith
  apply continuousOn_tsum (u := fun p : Nat.Primes ↦ (p * (p-1):ℝ)⁻¹)
  · intro p
    apply ContinuousOn.sub
    · apply Real.continuousOn_log.comp
      · apply continuousOn_inv₀.comp
        · apply Continuous.continuousOn
          apply Continuous.sub
          · fun_prop
          apply hcont
        intro σ
        simp only [Set.mem_Ici, neg_add_rev, Set.mem_compl_iff, Set.mem_singleton_iff]
        apply mt
      · intro σ
        simp only [Set.mem_Ici, neg_add_rev, Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]
        apply mt
    · apply hcont.continuousOn
  · apply summable_aux.subtype
  · intro p σ hσ
    rw [f_term_eq_tsum', norm_eq_abs, abs_of_nonneg]
    · simp only [Set.mem_Ici] at hσ
      apply (f_term_mono _ hσ).trans
      apply tsum_inv_pow_div_id_le_nat
      exact_mod_cast p.2.one_lt
    · positivity
    · simpa using hσ

theorem f_zero : f 0 = M := by
  simp [f_eq_tsum_tsum _ le_rfl, M, rpow_neg, tsum_subtype]
  trans ∑' p : {n : ℕ | n.Prime}, ∑' n : ℕ, ((p:ℕ)^(n+2):ℝ)⁻¹/(n+2)
  · rfl
  rw [tsum_subtype {n : ℕ | n.Prime} (fun k ↦ ∑' n : ℕ, (((k:ℝ)^(n+2))⁻¹/(n+2))) ]
  simp [Set.indicator_apply]

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
