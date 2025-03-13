import Mathlib.MeasureTheory.Integral.Asymptotics

import Analytic.Mathlib.MeasureTheory.Integral.IntegrableOn

open Asymptotics MeasureTheory Set Filter

variable {α E F : Type*} [NormedAddCommGroup E] {f : α → E} {g : α → F} {a : α} {l : Filter α}

namespace Asymptotics

section Basic

variable [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}

theorem IsBigO.integrableOn (s : Set α) (hs : MeasurableSet s) (hf : f =O[𝓟 s] g)
    (hfm : AEStronglyMeasurable f (μ.restrict s)) (hg : IntegrableOn g s μ) :
    IntegrableOn f s μ := by
  rw [← integrableAtFilter_principal_iff] at hg ⊢
  rw [← principal_isMeasurablyGenerated_iff] at hs
  apply hf.integrableAtFilter _ hg
  apply AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hfm
  exact fun ⦃a⦄ a ↦ a
