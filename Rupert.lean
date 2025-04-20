import Mathlib
open Matrix

abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)
abbrev TwoSpace := EuclideanSpace ℝ (Fin 2)

notation "ℝ³" => ThreeSpace
notation "ℝ²" => TwoSpace

def project32 (v : ℝ³) : ℝ² := ![v 0, v 1]

def IsRupert (p : Set ℝ³) : Prop := 
   let SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ
   ∃ R₁ ∈ SO3, ∃ R₂ ∈ SO3, ∃ T : ℝ², 
   let Im₁ := Set.image (λ t ↦ project32 (R₁ *ᵥ t)) p
   let Im₂ := Set.image (λ t ↦ T + project32 (R₂ *ᵥ t)) p
   Im₂ ⊆ interior Im₁
