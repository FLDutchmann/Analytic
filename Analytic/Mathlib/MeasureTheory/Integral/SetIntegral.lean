import Mathlib.MeasureTheory.Integral.SetIntegral


noncomputable section

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology
open scoped ENNReal NNReal

variable {X Y E F : Type*}

namespace MeasureTheory

variable {mX : MeasurableSpace X}

section NormedAddCommGroup

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : X → E} {s t : Set X} {μ : Measure X}

theorem setIntegral_mono_on_fun_of_nonneg {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → ℝ} {s : Set X} (hf : AEStronglyMeasurable f (μ.restrict s))
    (hg : IntegrableOn g s μ) (hs : MeasurableSet s) (h : ∀ x ∈ s, f x ≤ g x)
    (h_nonneg : ∀ x ∈ s, 0 ≤ f x) :
    ∫ (x : X) in s, f x ∂μ ≤ ∫ (x : X) in s, g x ∂μ := by
  apply MeasureTheory.setIntegral_mono_on _ hg hs h
  rw [IntegrableOn]
  apply MeasureTheory.Integrable.mono hg hf
  filter_upwards [self_mem_ae_restrict hs]
  intro x hx
  simp only [Real.norm_of_nonneg, h_nonneg x hx, (h_nonneg x hx).trans (h x hx)]
  exact h x hx
