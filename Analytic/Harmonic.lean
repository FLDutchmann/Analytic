import Mathlib

open Filter Asymptotics Real

local notation "γ" => eulerMascheroniConstant
theorem harmonic_estimate :
    (fun t : ℝ ↦ harmonic ⌊t⌋₊ - Real.log t - γ) =O[𝓟 (Set.Ici 1)] (fun t : ℝ ↦ t⁻¹) := by
  sorry
