import Analytic.Mertens
import Analytic.Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

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

theorem log_add_id_IsBigO_nhdsWithin_id :
    (fun x ↦ log (1 + x)) =O[𝓝 0] fun x ↦ x := by
  rw [Asymptotics.isBigO_iff']
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_abs_sub_lt 0 (show 0 < 1/2 by norm_num)] with x hx
  simp only [Set.mem_Ioi, norm_eq_abs] at ⊢ hx
  simp only [sub_zero, one_div] at hx
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by simp only [abs_neg]; linarith) 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_neg_eq_add, zero_add, abs_neg,
    pow_one] at h
  have : 1/2 ≤ 1 - |x| := by
    linarith
  apply h.trans
  rw [div_le_iff₀]
  calc _ = 2 * |x| * (1/2) := by ring
    _ ≤ _ := by gcongr
  linarith

example (f : ℝ → ℝ) (hf : f =O[𝓝 0] (fun x ↦ x)) :
    (fun x ↦ log (1 + f x)) =O[𝓝 0] (fun x ↦ x) := by
  have := log_add_id_IsBigO_nhdsWithin_id.comp_tendsto (k := f) (l' := 𝓝 0)
  simp [Function.comp_def] at this
  apply (this _).trans hf
  apply hf.trans_tendsto
  apply continuous_id.tendsto

theorem isBigO_log_one_add (f : ℝ → ℝ) (hf : f =O[𝓝[>] 0] (fun x ↦ x)) :
    (fun x ↦ log (1 + f x)) =O[𝓝[>] 0] (fun x ↦ x) := by
  have := log_add_id_IsBigO_nhdsWithin_id.comp_tendsto (k := f) (l' := 𝓝[>] 0)
  simp [Function.comp_def] at this
  apply (this _).trans hf
  apply hf.trans_tendsto
  apply Filter.Tendsto.mono_left (continuous_id.tendsto 0)
  exact nhdsWithin_le_nhds

-- TBD: right conditions on l
theorem est_log (f : ℝ → ℝ) (hf : ∀ᶠ x in 𝓝[>] 0, f x ≠ 0)
    (hfg : (fun x ↦ f x - x⁻¹) =O[𝓝[>] 0] (fun _ ↦ (1:ℝ))) :
    (fun x ↦ log (f x) - log (x⁻¹)) =O[𝓝[>] 0] (fun x ↦ x) := by
  have := isBigO_log_one_add (fun x ↦ x * f x - 1) ?side
  case side =>
    have := hfg.mul (isBigO_refl (fun x ↦ x) _)
    apply this.congr'
    · filter_upwards [eventually_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi] at hx
      simp [sub_mul, hx.ne.symm, mul_comm x]
    · simp
  apply this.congr' ?_ (by rfl)
  filter_upwards [eventually_mem_nhdsWithin, hf] with x hx hfx
  simp only [Set.mem_Ioi] at hx
  ring_nf
  rw [Real.log_mul hx.ne.symm hfx, Real.log_inv]
  ring

theorem est_1 : (fun σ ↦ log (zeta (1 + σ)) - log (σ⁻¹)) =O[𝓝[>] 0] (fun σ ↦ σ) := by
  apply est_log _ _ zeta_pole_estimate_nhdsWithin
  filter_upwards [eventually_mem_nhdsWithin] with x hx
  simp only [Set.mem_Ioi] at hx
  apply zeta_ne_zero
  linarith only [hx]


theorem inv_sub_one_isBigO_pow
    {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hf : (fun x ↦ f x - 1) =O[𝓝 0] fun x ↦ x^a) :
    (fun x ↦ (f x)⁻¹ - 1) =O[𝓝 0] fun x ↦ x^a := by
  have : Tendsto f (𝓝 0) (𝓝 1) := by
    have := hf.trans_tendsto ?side
    case side =>
      convert (Real.continuousAt_rpow_const _ _ _).tendsto
      · simp [ha.ne.symm]
      · simp [ha.le]
    convert this.add (tendsto_const_nhds (x := 1)) using 1
    · ext x
      ring
    simp
  have hf_ne_zero : ∀ᶠ x in 𝓝 0, f x ≠ 0 := by
    exact this.eventually_ne (by norm_num)
  have : (fun _ ↦ (1:ℝ)) =O[𝓝 0] f := by
    apply Asymptotics.isBigO_of_div_tendsto_nhds (c := 1)
    · simp [Pi.div_def]
      simpa using Tendsto.inv₀ this
    · simpa using hf_ne_zero
  apply (hf.mul (this.inv_rev (by simp))).neg_left.congr'
  · filter_upwards [hf_ne_zero]  with x hx
    simp [sub_mul, hx]
  · simp

theorem inv_sub_one_isBigO_pow' {l : Filter ℝ} (hl : l ≤ 𝓝 0)
    {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hf : (fun x ↦ f x - 1) =O[l] fun x ↦ x^a) :
    (fun x ↦ (f x)⁻¹ - 1) =O[l] fun x ↦ x^a := by
  have : Tendsto f l (𝓝 1) := by
    have := hf.trans_tendsto ?side
    case side =>
      apply Tendsto.mono_left _ hl
      convert (Real.continuousAt_rpow_const _ _ _).tendsto
      · simp [ha.ne.symm]
      · simp [ha.le]
    convert this.add (tendsto_const_nhds (x := 1)) using 1
    · ext x
      ring
    simp
  have hf_ne_zero : ∀ᶠ x in l, f x ≠ 0 := by
    exact this.eventually_ne (by norm_num)
  have : (fun _ ↦ (1:ℝ)) =O[l] f := by
    apply Asymptotics.isBigO_of_div_tendsto_nhds (c := 1)
    · simp [Pi.div_def]
      simpa using Tendsto.inv₀ this
    · simpa using hf_ne_zero
  apply (hf.mul (this.inv_rev (by simp))).neg_left.congr'
  · filter_upwards [hf_ne_zero]  with x hx
    simp [sub_mul, hx]
  · simp

theorem inv_sub_pow_isBigO {f : ℝ → ℝ} {a b : ℝ} (hb : a < b) (hf : (fun x ↦ f x - x^a) =O[𝓝[>] 0] fun x ↦ x^b) :
    (fun x ↦ (f x)⁻¹ - x^(-a)) =O[𝓝[>] 0] fun x ↦ x^(b-2*a) := by
  have := inv_sub_one_isBigO_pow' (f := fun x ↦ x ^ (-a) * f x)  (a := (b-a)) ?filter (by linarith)
    (l := 𝓝[>] 0) ?side
  case filter =>
    exact nhdsWithin_le_nhds
  case side =>
    apply (hf.mul (isBigO_refl (fun x ↦ x ^ (-a)) _)).congr'
    · filter_upwards [eventually_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi] at hx
      simp [sub_mul, hx, ← Real.rpow_add, mul_comm]
    · filter_upwards [eventually_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi] at hx
      rw [← Real.rpow_add hx]
      ring_nf
  simp [mul_inv_rev, rpow_neg] at this
  apply this.mul (isBigO_refl (fun x ↦ x ^ (-a)) _) |>.congr'
  · filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [Set.mem_Ioi] at hx
    simp [sub_mul, mul_assoc, ]
    rw [inv_mul_cancel₀]
    · simp
    · positivity
  · filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [Set.mem_Ioi] at hx
    rw [← rpow_add hx]
    ring_nf

theorem extracted_1 : (fun x ↦ 1 - rexp (-x) - x ^ 1) =O[𝓝 0] fun x ↦ x ^ 2 := by
  have := Real.exp_sub_sum_range_isBigO_pow 2 |>.neg_left
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero,
    Nat.factorial_zero, Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, pow_one,
    Nat.factorial_one, div_one, Nat.factorial_two, Nat.cast_ofNat] at this
  have ht : Tendsto (fun x : ℝ ↦ -x) (𝓝 0) (𝓝 0) := by
    convert continuous_neg.tendsto (0:ℝ)
    simp
  have := this.comp_tendsto ht
  apply this.congr
  · intro x
    simp only [neg_sub, Function.comp_apply, pow_one]
    ring
  · simp

theorem est_2 : (fun σ ↦ log ((1-exp (-σ))⁻¹) - log (σ⁻¹)) =O[𝓝[>] 0] (fun σ ↦ σ) := by
  apply est_log
  · filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [Set.mem_Ioi] at hx
    apply inv_ne_zero
    rw [ne_eq, sub_eq_zero, eq_comm]
    simp [exp_eq_one_iff, neg_eq_zero, hx.ne.symm]
  convert_to (fun x ↦ (1 - rexp (-x))⁻¹ - x^(-1:ℝ)) =O[𝓝[>] 0] fun x ↦ x^(2 - 2 * 1:ℝ) using 0
  · apply Asymptotics.isBigO_congr
    · filter_upwards [eventually_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi] at hx
      simp [rpow_neg, hx.le]
    · simp
  apply inv_sub_pow_isBigO
  · simp
  norm_cast
  apply extracted_1.mono nhdsWithin_le_nhds

theorem est_3_hasSum {σ : ℝ} (hσ : 0 < σ) : HasSum (fun n : ℕ ↦ exp (- σ * n) * (n : ℝ)⁻¹) (log ((1 - exp (-σ))⁻¹)) := by
  have := hasSum_pow_div_log_of_abs_lt_one (show |exp (-σ)| < 1 by simp [hσ])
  norm_cast at this
  rw [hasSum_nat_add_iff 1 (f := fun n ↦ exp (-σ)^n / n)] at this
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, CharP.cast_eq_zero, div_zero,
    add_zero] at this
  convert this using 1
  · ext n
    rw [exp_mul, rpow_natCast]
    ring
  simp

-- hasSum_pow_div_log_of_abs_lt_one
theorem est_3 {σ : ℝ} (hσ : 0 < σ) : log ((1 - exp (- σ))⁻¹) = ∑' n : ℕ, exp (- σ * n) * (n : ℝ)⁻¹ := by
  rw [est_3_hasSum hσ |>.tsum_eq]

/- This one's a little annoying. Use [1] to get the limit of the partial sums, then use [2] to get the value
of the tsum. https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/NatInt.html#Summable.tendsto_sum_tsum_nat

[1](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/AbelSummation.html#sum_mul_eq_sub_integral_mul₀)
[2](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/NatInt.html#Summable.tendsto_sum_tsum_nat)
-/

theorem harmonic_eq_sum_range_succ (n : ℕ) : harmonic n = ∑ i ∈ Finset.range (n + 1), (i : ℚ)⁻¹ := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp  [ih, Finset.sum_range_succ]

theorem harmonic_nonneg (n : ℕ) : 0 ≤ harmonic n := by
  rw [harmonic]
  positivity

theorem harmonic_isBigO_log : (fun x : ℝ ↦ (harmonic ⌊x⌋₊:ℝ)) =O[atTop] Real.log := by
  trans (fun x ↦ 1 + Real.log x)
  · apply Filter.Eventually.isBigO
    filter_upwards [eventually_ge_atTop 1] with x hx
    simp only [Rat.norm_cast_real, norm_eq_abs]
    rw [abs_of_nonneg (mod_cast (harmonic_nonneg _))]
    apply harmonic_floor_le_one_add_log _ hx
  rw [IsBigO.add_iff_left (isBigO_refl ..)]
  apply (Real.isLittleO_const_log_atTop).isBigO

/- Note: really need the integral from 0, I think. -/
theorem est_4 {σ : ℝ} (hσ : 0 < σ) :
    ∑' n : ℕ, exp ((-σ) * n) * (n : ℝ)⁻¹ = σ * ∫ t in Set.Ioi 1, exp ((-σ) * t) * harmonic (⌊t⌋₊) := by
  let c (n : ℕ) : ℝ := (n : ℝ)⁻¹
  let f (x : ℝ) := exp ((-σ) * x)
  let f' (x : ℝ) := (-σ) * exp ((-σ) * x)
  let g (x : ℝ) := exp ((-σ) * x) * (Real.log x)
  have hf (x : ℝ) : HasDerivAt f (f' x) x := by
    simp only [f]
    convert (hasDerivAt_exp ((-σ) * x)).comp x ((hasDerivAt_id' x).const_mul (-σ)) using 1
    ring
  have hc_sum (n : ℕ) : ∑ i ∈ Finset.Icc 0 n, c i = harmonic n := by
    rw [harmonic_eq_sum_Icc, eq_comm]
    simp [c]
    apply Finset.sum_subset
    · apply Finset.Icc_subset_Icc <;> norm_num
    intro x hx hx'
    simp only [inv_eq_zero, Nat.cast_eq_zero, f, c]
    simp only [Finset.mem_Icc, zero_le, true_and, not_and, not_le, f, c] at hx hx'
    omega
  have hbigO_deriv : (fun t ↦ deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop] g := by
    simp_rw [deriv_eq hf, f', g]
    apply IsBigO.mul
    · apply IsBigO.const_mul_left
      exact isBigO_refl (fun x ↦ rexp (-σ * x)) atTop
    · simp_rw [hc_sum]
      exact harmonic_isBigO_log
  have hbigO : (fun (t : ℝ) ↦ f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop] g := by
    have h : f =O[atTop] deriv f := by
      simp_rw [deriv_eq hf, f, f']
      apply IsBigO.const_mul_right
      · linarith
      exact isBigO_refl (fun x ↦ rexp (-σ * x)) atTop
    apply IsBigO.trans _ hbigO_deriv
    apply h.mul (isBigO_refl ..)
  have hf_isBigO : f =O[atTop] (fun x ↦ x^(-7:ℝ)) := by
    apply isLittleO_exp_neg_mul_rpow_atTop hσ (-7)|>.isBigO
  have hg_isBigO : g =O[atTop] (fun x ↦ x ^ (-5:ℝ)) := by
    have := isBigO_rpow_top_log_smul (show (5 : ℝ) < (7 : ℝ) by norm_num) hf_isBigO
    apply this.congr'
    · filter_upwards with x
      simp only [neg_mul, smul_eq_mul, f, g, f']
      ring
    · exact Eq.eventuallyEq rfl
  have htends := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c (by norm_num) (f := f) ?hf_diff (l := 0) ?hf_int ?hlim (g := g) hbigO_deriv ?hg_int
  case hf_diff =>
    intro t _
    apply (hf _).differentiableAt
  case hf_int =>
    simp_rw [deriv_eq hf, f']
    apply MeasureTheory.LocallyIntegrableOn.continuousOn_mul
    · apply MeasureTheory.IntegrableOn.locallyIntegrableOn
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      apply ((exp_neg_integrableOn_Ioi 1 hσ))
    · exact continuousOn_const
    · exact isLocallyClosed_Ici
  case hlim =>
    convert (hbigO.trans_tendsto _).comp (tendsto_natCast_atTop_atTop) with n
    · simp
    apply hg_isBigO.trans_tendsto
    refine tendsto_rpow_neg_atTop ?_
    norm_num
  case hg_int =>
    apply hg_isBigO.integrableAtFilter
    · simp_rw [g]
      apply (Measurable.stronglyMeasurable _).stronglyMeasurableAtFilter
      fun_prop
    · rw [integrableAtFilter_rpow_atTop_iff]
      norm_num
  simp_rw [← Nat.range_succ_eq_Icc_zero] at htends
  have hsummable : Summable (fun n : ℕ ↦ f n * c n) := by
    have : c =O[atTop] fun x ↦ (1:ℝ) := by
      simp_rw [c, ← Real.rpow_neg_one]
      apply IsBigO.natCast_atTop (f := fun x : ℝ ↦ x ^ _) (g := fun _ ↦ 1)
      convert (isBigO_rpow_rpow_atTop_of_le (show -1 ≤ (0:ℝ) by norm_num)) using 1
      simp
    have := (hf_isBigO.natCast_atTop).mul this
    apply summable_of_isBigO_nat _ this
    simp only [mul_one, summable_nat_rpow, neg_lt_neg_iff, Nat.one_lt_ofNat, f', g, f]
  have := (Summable.tendsto_sum_tsum_nat hsummable).comp (tendsto_add_atTop_nat 1)
  simp only [f', f, c, Function.comp_def] at this
  have := tendsto_nhds_unique htends this
  rw [← this]
  simp_rw [harmonic_eq_sum_range_succ, c, deriv_eq hf, f']
  push_cast
  simp only [neg_mul, zero_sub, g, f, f', c, ← MeasureTheory.integral_mul_left, ← MeasureTheory.integral_neg]
  simp
  congr 2 with t
  ring

theorem est_log_zeta :
    (fun σ ↦ log (zeta (1 + σ)) - σ * ∫ t in Set.Ioi 1, exp (- σ * t) * harmonic (⌊t⌋₊)) =O[𝓝[>] 0]
      (fun σ ↦ σ) := by
  apply (est_1.triangle est_2.symm).congr'
  · filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [Set.mem_Ioi] at hx
    simp only [est_3, est_4, hx]
  · rfl

noncomputable def P (t : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), (p : ℝ)⁻¹

theorem P_eq : P = (fun t ↦ ∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), (p : ℝ)⁻¹) := rfl

theorem P_mono {x y : ℝ} (hxy : x ≤ y) : P x ≤ P y := by
  simp [P, Nat.primesBelow]
  gcongr

theorem P_nonneg (x : ℝ) : 0 ≤ P x := by
  simp [P]
  positivity

theorem P_isBigO_log : P =O[atTop] log := by
  trans (fun t ↦ (harmonic ⌊t⌋₊))
  · simp [P_eq, Nat.primesBelow, harmonic_eq_sum_Icc]
    apply IsBigO.of_bound'
    filter_upwards with x
    simp only [norm_eq_abs]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    gcongr
    intro p; simp
    intro hp hpp
    refine ⟨hpp.one_le, by omega⟩
  · exact harmonic_isBigO_log

theorem MeasureTheory.LocallyIntegrableOn.congr_on {X : Type*} {E : Type*} [MeasurableSpace X] [TopologicalSpace X] [TopologicalSpace E] [ContinuousENorm E] [NormedAddCommGroup E] {f g : X → E} {s : Set X} {μ : MeasureTheory.Measure X} (hfg : s.EqOn f g) (hf : LocallyIntegrableOn f s μ) : LocallyIntegrableOn g s μ  := by
  -- rw [MeasureTheory.IntegrableOn.eq_1] at hf ⊢
  sorry

theorem tsum_primes {f : ℕ → ℝ} : ∑' p : Nat.Primes, f p = ∑' n : ℕ, if n.Prime then f n else 0 := by
  simp_rw [Nat.Primes]
  -- have := show ({p // Nat.Prime p}) = ({p | Nat.Prime p} : Set ℕ) by sorry
  erw [tsum_subtype]
  classical
  simp [Set.indicator_apply]
  congr with x
  have : Irreducible x ↔ Nat.Prime x := by
    sorry







  sorry

theorem est_P {σ : ℝ} (hσ : 0 < σ) :
    ∑' p : Nat.Primes, (p : ℝ)⁻¹ ^(1+σ) = σ * ∫ t in Set.Ioi 1, t ^ (-σ - 1) * P t := by
  let c (n : ℕ) : ℝ := if n.Prime then (n : ℝ)⁻¹ else 0
  let f (x : ℝ) := x ^ (-σ)
  let f' (x : ℝ) := (-σ) * x ^ (-σ - 1)
  have hf' {x : ℝ} (hx : x ≠ 0) : HasDerivAt f (f' x) x := by
    simp_rw [f, f']
    apply Real.hasDerivAt_rpow_const (p := -σ)
    simp [hx]
  have hderiv_f : (Set.Ici (1:ℝ)).EqOn (deriv f) f' := by
    intro x hx
    simp only [Set.mem_Ici, f', f] at hx
    rw [hf' (by linarith) |>.deriv]
  -- have deriv_f_eq : deriv f = f' := by
  --   simp [f, f']
  --   · simp [hx, f, f']

  --     sorry
  --   sorry
  let g (x : ℝ) := x ^ (-σ-1) * (Real.log x)
  have g_isBigO : (fun x ↦ g x) =O[atTop] (fun x ↦ x ^ (-σ/2 - 1)) := by
    sorry
  have hc_sum (n : ℕ) : ∑ i ∈ Finset.Icc 0 n, c i = P n := by
    simp [P, c, ← Finset.sum_filter]
    congr
    exact (Nat.range_succ_eq_Icc_zero n).symm

              -- tendsto_sum_mul_atTop_nhds_one_sub_integral
  have htends := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c (by simp [c]) (f := f) ?hf_diff (l := 0) ?hf_int ?hlim (g := g) ?isBigO_g ?hg_int
  case isBigO_g =>
    simp_rw [g, hc_sum]
    calc
      _ =ᶠ[atTop] (fun x ↦ f' x * P (⌊x⌋₊)) := by
        filter_upwards [eventually_ne_atTop 0] with x hx
        congr
        rw [(hf' hx).deriv]
      _ =O[atTop] _ := by
        apply IsBigO.mul
        · simp [f']
          apply IsBigO.of_bound σ
          simp [abs_of_pos hσ]
        · trans P
          · apply IsBigO.of_bound'
            simp [abs_of_nonneg, P_nonneg]
            use 0
            intro x hx
            apply P_mono
            exact Nat.floor_le hx
          exact P_isBigO_log
  case hf_diff =>
    simp only [Set.mem_Ici]
    intro t ht
    apply (hf' _).differentiableAt
    linarith
  case hf_int =>
    apply MeasureTheory.LocallyIntegrableOn.congr_on hderiv_f.symm
    simp [f']
    apply ContinuousOn.locallyIntegrableOn
    · apply ContinuousOn.neg
      apply ContinuousOn.mul
      · exact continuousOn_const
      apply ContinuousOn.rpow
      · exact continuousOn_id' (Set.Ici 1)
      · exact continuousOn_const
      · simp +contextual
        intro x hx
        left
        linarith
    measurability
  case hlim =>
    have hisBigO_log_smul : (fun n : ℕ ↦ f n * ∑ i ∈ Finset.Icc 0 n, c i) =O[atTop]  (fun t ↦ log t • (t:ℝ)^(-σ)) := by
      simp
      conv =>
        enter [2, n]
        rw [mul_comm]
      apply IsBigO.mul
      · simp_rw [hc_sum]
        apply P_isBigO_log.natCast_atTop
      · apply isBigO_refl
    have hf : f =O[atTop] (fun t ↦ t ^ (- σ)) := isBigO_refl ..

    -- by simp [f]; apply IsBigO.rfl
    have := isBigO_rpow_top_log_smul (b := σ / 2) (a := σ) (by linarith) hf
    have := hisBigO_log_smul.trans (this.natCast_atTop) |>.trans_tendsto
    apply this
    apply tendsto_rpow_neg_atTop (by linarith) |>.comp tendsto_natCast_atTop_atTop
  case hg_int =>
    apply g_isBigO.integrableAtFilter (μ := MeasureTheory.volume)
    · simp [g]
      apply MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter
      apply Measurable.stronglyMeasurable
      fun_prop
    rw [integrableAtFilter_rpow_atTop_iff]
    linarith
  simp_rw [hc_sum] at htends
-- [2](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/InfiniteSum/NatInt.html#Summable.tendsto_sum_tsum_nat)
  have {n : ℕ} : f n * c n = if n.Prime then (n : ℝ)^(-σ-1) else 0 := by
    simp_rw [f, c]
    split_ifs with h
    · rw [← rpow_neg_one, ← rpow_add]
      · ring_nf
      · norm_cast
        apply h.pos
    · simp
  simp_rw [← Nat.range_succ_eq_Icc_zero, this] at htends
  sorry

#check MeasureTheory.integral_comp_mul_deriv_Ioi
theorem est_P_rexp {σ : ℝ} (hσ : 0 < σ) :
    ∑' p : Nat.Primes, (p : ℝ)⁻¹ ^(1+σ) = σ * ∫ t in Set.Ioi 0, exp ((-σ) * t) * P (exp t) := by
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
