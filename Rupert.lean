import Mathlib

open scoped Matrix

notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- Projects a vector from `ℝ³` to `ℝ²` by ignoring the third coordinate. -/
def project32 (v : ℝ³) : ℝ² := ![v 0, v 1]

/-- The Rupert Property for a convex polyhedron given as a set of vertices. -/
def IsRupert (p : Set ℝ³) : Prop :=
   ∃ inner_rot ∈ SO3, ∃ outer_rot ∈ SO3, ∃ inner_offset : ℝ²,
   have inner_shadow := Set.image (λ t ↦ inner_offset + project32 (inner_rot *ᵥ t)) p
   have outer_shadow := Set.image (λ t ↦ project32 (outer_rot *ᵥ t)) p
   inner_shadow ⊆ interior (convexHull ℝ outer_shadow)

section square_is_rupert
def square : Set ℝ³ := { ![-1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, 0] }

/- In this section we aim to show that the square has the rupert property.
   Status:  
   - Still need to show that the desired rotations are actually in SO(3)
   - Still need to show that the shadow of any point from the inner square is in the 
     shadow of the outer square.
-/
 open Matrix 
 open Real

theorem square_is_rupert : IsRupert square := by

/-

The diagram shows the (x,y) plane, the z axis runs through the
screen. The rotation inner_rot rotates about the x axis, creating the
horizontal slot shape.  The rotation outer_rot rotates the (x,y) plane
by π/4 radians. No offset translation is needed.

      +
     / \
    /   \
   /     \
  + ----- +
   \     /
    \   /
     \ /
      +
-/
 let inner_rot : Matrix (Fin 3) (Fin 3) ℝ := 
   !![1, 0, 0;
      0, 0,-1;
      0, 1, 0]
 let outer_rot : Matrix (Fin 3) (Fin 3) ℝ := 
   !![0, sqrt 2, 0;
      -sqrt 2, 0, 0;
      0, 0, 1]
 let inner_offset : ℝ² := λ _ => 0

 have inner_rot_so3 : inner_rot ∈ SO3 := by
   have inner_rot_unitary : inner_rot ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
     change star inner_rot * inner_rot = 1 ∧ inner_rot * star inner_rot = 1
     constructor
     · -- to show: star inner_rot * inner_rot = 1
       simp [inner_rot]
       -- some ideas here:
       -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/the.20identity.20matrix.20and.20decidable.20equality
       ext i j; simp [ Matrix.one_apply, Matrix.star_apply]
       sorry
     · -- to show: inner_rot * star inner_rot = 1
       sorry
   constructor
   · exact inner_rot_unitary
   · simp [inner_rot, det_succ_row_zero, Fin.sum_univ_succ]

 have outer_rot_so3 : outer_rot ∈ SO3 := sorry

 use inner_rot, inner_rot_so3, outer_rot, outer_rot_so3, inner_offset

 intro inner_shadow outer_shadow x ⟨y, ⟨y_in_square, proj_rot_y_eq_x ⟩⟩
 -- we have y ∈ ℝ³ that came from the square, which after being rotated by
 -- inner_rot and projected, is x
 rw [← proj_rot_y_eq_x]; unfold inner_offset; simp; 
 sorry

end square_is_rupert
