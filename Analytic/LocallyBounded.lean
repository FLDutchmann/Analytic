import Mathlib

open Real Asymptotics MeasureTheory Filter

section MeasureTheory
variable {α : Type*} {E : Type*} {F : Type*} [TopologicalSpace α] [Norm E] [Norm F]

def Asymptotics.IsLocallyBigO  (l : Filter α) (f : α → E) (g : α → F) :
  Prop :=
  ∀ᶠ x in l, f =O[l ⊓ (nhds x)] g

theorem lemma1 (f : α → E) (g : α → F) (l : Filter α) (h : f =O[cocompact α] g) (h' : IsLocallyBigO ⊤ f g) :
  f =O[⊤] g := by
  obtain ⟨c, h⟩ := h.isBigOWith
  rw [IsBigOWith, Filter.Eventually, mem_cocompact] at h
  obtain ⟨t, ht, htc⟩ := h
  rw [IsLocallyBigO] at h'
  simp only [le_top, inf_of_le_right, eventually_top, ]  at h'
  simp only [IsBigO, IsBigOWith, Filter.eventually_iff_exists_mem] at h'
  choose C h using h'
  choose U hU hU' using h
  obtain ⟨s, hs, ht_sub⟩ := ht.elim_nhds_subcover U (fun x _ ↦ hU x)
  by_cases hs_empty : s = ∅
  · simp_all
    have (x : α) := Set.mem_univ x
    simp [← htc] at this
    exact ⟨c, this⟩
  simp only at hs_empty
  simp only [isBigO_top]
  use max c (s.sup' (Finset.nonempty_of_ne_empty hs_empty) C )
  --yes this works but the proof needs polishing
  sorry

example (f g : ℝ → ℝ) (a : ℝ) (s : Set ℝ) (hs : BddBelow s)
  (h : f =O[atTop] g) (h' : IsLocallyBigO (𝓟 s) f g) : f =O[𝓟 s] g := by
  let f' := s.indicator f
  let g' := s.indicator g
  have := lemma1 f' g' (𝓟 s) ?_ ?_
  · apply (this.mono (le_top (a := 𝓟 s))).congr' <;>
    · rw [eventuallyEq_principal]
      apply Set.eqOn_indicator
  · simp only [cocompact_eq_atBot_atTop, isBigO_sup]
    sorry
  rw [IsLocallyBigO] at h' ⊢
  sorry

def IsLocallyBoundedAtFilter (l : Filter α) (f : α → E) : Prop :=
    IsLocallyBigO l f (fun _ ↦ (1:ℝ))




end MeasureTheory
