import Mathlib
import Rupert.Basic
open Pointwise
open Matrix

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Projecting from ℝ³ to ℝ² is linear -/
def projection_linear : ℝ³ →ₗ[ℝ] ℝ² :=
  ⟨ ⟨ dropz, by sorry⟩ , by sorry⟩

/-- Applying a rotation matrix is linear.
    (Should be easy, applying any matrix is linear!) -/
def rotation_linear (rot : SO3) : ℝ³ →ₗ[ℝ] ℝ³ :=
  ⟨ ⟨ λ p => rot *ᵥ p, by sorry⟩ , by sorry⟩

/-- Translating is linear. -/
noncomputable
def offset_linear (off : E 2) : ℝ² →ₗ[ℝ] ℝ² :=
  ⟨ ⟨ λ p => off + p, by sorry⟩ , by sorry⟩

def projection_rotation_is_linear (rot : SO3) : ℝ³ →ₗ[ℝ] ℝ² :=
  LinearMap.comp projection_linear (rotation_linear rot)

noncomputable
def offset_transform_is_linear (off : E 2) (rot : SO3) : ℝ³ →ₗ[ℝ] ℝ² :=
  LinearMap.comp (offset_linear off) (projection_rotation_is_linear rot)

theorem rupert_imp_rupert' {ι : Type} [Fintype ι] (v : ι → ℝ³) : IsRupert v → IsRupert' v := by
 intro ⟨ outer_rot,  outer_so3, inner_rot, inner_so3, offset, rupert⟩
 use outer_rot, outer_so3, inner_rot, inner_so3, offset
 let raw_outer_shadow := Set.range fun i ↦ dropz (outer_rot *ᵥ v i)
 let raw_inner_shadow := Set.range fun i ↦ offset + dropz (inner_rot *ᵥ v i)
 let hull := convexHull ℝ (Set.range v)
 let outer_shadow := (fun p ↦ dropz (outer_rot *ᵥ p)) '' hull
 let inner_shadow := (fun p ↦ offset + dropz (inner_rot *ᵥ p)) '' hull
 have inner_lemma : convexHull ℝ raw_inner_shadow = inner_shadow := by
   dsimp only [raw_inner_shadow, inner_shadow, hull]
   symm; rw [Set.range_comp' (fun p ↦ offset + dropz (inner_rot *ᵥ p)) v]
   apply (LinearMap.image_convexHull (offset_transform_is_linear offset ⟨inner_rot, inner_so3⟩))
 have outer_lemma : convexHull ℝ raw_outer_shadow = outer_shadow := by
   dsimp only [raw_outer_shadow, outer_shadow, hull]
   symm; rw [Set.range_comp' (fun p ↦ dropz (outer_rot *ᵥ p)) v]
   apply (LinearMap.image_convexHull (projection_rotation_is_linear ⟨outer_rot, outer_so3⟩))

 change raw_inner_shadow ⊆ interior (convexHull ℝ raw_outer_shadow) at rupert
 change inner_shadow ⊆ interior outer_shadow
 rw [← inner_lemma, ← outer_lemma]
 let interior_convex : Convex ℝ (interior (convexHull ℝ raw_outer_shadow)) :=
    Convex.interior (convex_convexHull ℝ raw_outer_shadow)
 exact (Convex.convexHull_subset_iff interior_convex).mpr rupert

theorem rupert'_imp_rupert {ι : Type} [Fintype ι] (v : ι → ℝ³) : IsRupert' v → IsRupert v := by
 intro ⟨ outer_rot,  outer_so3, inner_rot, inner_so3, offset, rupert⟩
 use outer_rot, outer_so3, inner_rot, inner_so3, offset
 let raw_outer_shadow := Set.range fun i ↦ dropz (outer_rot *ᵥ v i)
 let raw_inner_shadow := Set.range fun i ↦ offset + dropz (inner_rot *ᵥ v i)
 let hull := convexHull ℝ (Set.range v)
 let outer_shadow := (fun p ↦ dropz (outer_rot *ᵥ p)) '' hull
 let inner_shadow := (fun p ↦ offset + dropz (inner_rot *ᵥ p)) '' hull
 have inner_lemma : convexHull ℝ raw_inner_shadow = inner_shadow := by
   dsimp only [raw_inner_shadow, inner_shadow, hull]
   symm; rw [Set.range_comp' (fun p ↦ offset + dropz (inner_rot *ᵥ p)) v]
   apply (LinearMap.image_convexHull (offset_transform_is_linear offset ⟨inner_rot, inner_so3⟩))
 have outer_lemma : convexHull ℝ raw_outer_shadow = outer_shadow := by
   dsimp only [raw_outer_shadow, outer_shadow, hull]
   symm; rw [Set.range_comp' (fun p ↦ dropz (outer_rot *ᵥ p)) v]
   apply (LinearMap.image_convexHull (projection_rotation_is_linear ⟨outer_rot, outer_so3⟩))

 change raw_inner_shadow ⊆ interior (convexHull ℝ raw_outer_shadow)
 change inner_shadow ⊆ interior outer_shadow at rupert
 rw [outer_lemma]
 rw [← inner_lemma] at rupert
 intro x hx
 exact rupert (subset_convexHull ℝ raw_inner_shadow hx)
