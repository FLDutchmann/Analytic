import Mathlib.MeasureTheory.Integral.IntegrableOn


noncomputable section

open Set Filter TopologicalSpace MeasureTheory Function

open scoped Topology Interval Filter ENNReal MeasureTheory

section

variable {α E F : Type*} [NormedAddCommGroup E] {f : α → E} {g : α → F} {a : α} {l : Filter α}

variable [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}

@[simp]
theorem integrableAtFilter_principal_iff {S : Set α} :
  IntegrableAtFilter f (𝓟 S) μ ↔ IntegrableOn f S μ := by
  rw [IntegrableAtFilter]
  simp only [mem_principal]
  refine ⟨fun ⟨s, hsS, hfs⟩ ↦ hfs.mono hsS le_rfl, fun h ↦ ⟨S, le_rfl, h⟩⟩

theorem MeasureTheory.IntegrableAtFilter.integrableOn_of_principal
    {α : Type*} {E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {f : α → E} {S : Set α}
    {mu : Measure α} (h : IntegrableAtFilter f (𝓟 S) mu) : IntegrableOn f S mu :=
  integrableAtFilter_principal_iff.mp h

theorem MeasureTheory.IntegrableOn.integrableAtFilter
    {α : Type*} {E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {f : α → E} {S : Set α}
    {mu : Measure α} (h : IntegrableOn f S mu) : IntegrableAtFilter f (𝓟 S) mu :=
  integrableAtFilter_principal_iff.mpr h

end

end
