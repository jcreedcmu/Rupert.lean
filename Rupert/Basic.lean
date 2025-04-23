import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix

notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- Projects a vector from `ℝ³` to `ℝ²` by ignoring the third coordinate. -/
def project32 (v : ℝ³) : ℝ² := ![v 0, v 1]

/-- The Rupert Property for a convex polyhedron given as an indexed finite set of vertices. -/
def IsRupert {ι : Type} [Fintype ι] (v : ι → ℝ³) : Prop :=
   ∃ inner_rot ∈ SO3, ∃ outer_rot ∈ SO3, ∃ inner_offset : ℝ²,
   let inner_shadow := Set.range (fun i ↦ inner_offset + project32 (inner_rot *ᵥ v i))
   let outer_shadow := Set.range (fun i ↦ project32 (outer_rot *ᵥ v i))
   inner_shadow ⊆ interior (convexHull ℝ outer_shadow)
