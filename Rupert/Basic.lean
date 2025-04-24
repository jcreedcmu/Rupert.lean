import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix

notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- Projects a vector from 3-space to 2-space by dropping the third coordinate. -/
def dropz {k : Type} [Field k] (v : EuclideanSpace k (Fin 3)) : EuclideanSpace k (Fin 2) :=
  ![v 0, v 1]

/-- The Rupert Property for a convex polyhedron given as an indexed finite set of vertices. -/
def IsRupert {ι : Type} [Fintype ι] (v : ι → ℝ³) : Prop :=
   ∃ outer_rot ∈ SO3, ∃ inner_rot ∈ SO3, ∃ inner_offset : ℝ²,
   let outer_shadow := Set.range (fun i ↦ dropz (outer_rot *ᵥ v i))
   let inner_shadow := Set.range (fun i ↦ inner_offset + dropz (inner_rot *ᵥ v i))
   inner_shadow ⊆ interior (convexHull ℝ outer_shadow)
