import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Filter Nat

theorem Asymptotics.IsLittleO.isEquivalent_of_log {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (hf : ∀ᶠ x in l, 0 < f x) (hg : ∀ᶠ x in l, 0 < g x)
    (h : (fun x ↦ Real.log (f x) - Real.log (g x)) =o[l] (fun _ ↦ (1 : ℝ))) :
    IsEquivalent l f g := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · rw [Asymptotics.isLittleO_one_iff] at h
    apply tendsto_exp_nhds_zero_nhds_one.comp h |>.congr'
    filter_upwards [hf, hg] with x hfx hgx
    simp only [Function.comp_apply, Pi.div_apply, exp_sub, Real.exp_log hfx, Real.exp_log hgx]
  · filter_upwards [hg] with x hgx
    exact hgx.ne.symm

theorem Asymptotics.IsEquivalent.log_sub_log_isLittleO_one {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (hf : ∀ᶠ x in l, f x ≠ 0) (hg : ∀ᶠ x in l, g x ≠ 0)
    (h : IsEquivalent l f g) :
    (fun x ↦ Real.log (f x) - Real.log (g x)) =o[l] (fun _ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one hg] at h
  rw [Asymptotics.isLittleO_one_iff]
  have : Tendsto Real.log (nhds 1) (nhds 0) := by
    convert Real.continuousAt_log _ |>.tendsto <;> simp
  apply this.comp h |>.congr'
  filter_upwards [hf, hg] with x hfx hgx
  simp only [Function.comp_apply, Pi.div_apply, Real.log_div hfx hgx]

theorem Asymptotics.isEquivalent_iff_log_sub_log {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (hf : ∀ᶠ x in l, 0 < f x) (hg : ∀ᶠ x in l, 0 < g x) :
    (fun x ↦ Real.log (f x) - Real.log (g x)) =o[l] (fun _ ↦ (1 : ℝ)) ↔ IsEquivalent l f g := by
  constructor
  · exact IsLittleO.isEquivalent_of_log hf hg
  · apply IsEquivalent.log_sub_log_isLittleO_one
    · filter_upwards [hf] with x hfx
      exact Ne.symm (_root_.ne_of_lt hfx)
    · filter_upwards [hg] with x hgx
      exact Ne.symm (_root_.ne_of_lt hgx)

theorem Asymptotics.IsLittleO.isEquivalent_exp {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (h : (fun x ↦ f x - g x) =o[l] (fun _ ↦ (1 : ℝ))) :
    IsEquivalent l (fun x ↦ Real.exp (f x)) (fun x ↦ Real.exp (g x)) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · rw [Asymptotics.isLittleO_one_iff] at h
    apply tendsto_exp_nhds_zero_nhds_one.comp h |>.congr'
    filter_upwards with x
    simp [Real.exp_sub]
  · filter_upwards with x
    exact exp_ne_zero (g x)

theorem Asymptotics.IsEquivalent.sub_isLittleO_one {ι : Type*} {l : Filter ι} {f g : ι → ℝ}
    (h : IsEquivalent l (fun x ↦ Real.exp (f x)) (fun x ↦ Real.exp (g x))) :
    (fun x ↦ f x - g x) =o[l] (fun _ ↦ (1 : ℝ)) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one] at h
  rw [Asymptotics.isLittleO_one_iff]
  have : Tendsto Real.log (nhds 1) (nhds 0) := by
    convert Real.continuousAt_log _ |>.tendsto <;> simp
  · apply this.comp h |>.congr'
    filter_upwards with x
    simp only [Function.comp_apply, Pi.div_apply, ← Real.exp_sub, Real.log_exp]
  · filter_upwards with x
    exact exp_ne_zero (g x)

theorem Asymptotics.isEquivalent_exp_iff_sub_isLittleO_one {ι : Type*} {l : Filter ι} {f g : ι → ℝ} :
    (IsEquivalent l (fun x ↦ Real.exp (f x)) (fun x ↦ Real.exp (g x))) ↔
    (fun x ↦ f x - g x) =o[l] (fun _ ↦ (1 : ℝ)) := by
  constructor
  · exact fun a ↦ a.sub_isLittleO_one
  · exact fun a ↦ a.isEquivalent_exp
