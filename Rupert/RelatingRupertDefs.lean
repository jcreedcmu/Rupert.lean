import Mathlib
import Rupert.Basic
open Pointwise
open Matrix

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)


/-- Projecting from ℝ³ to ℝ² is affine -/
noncomputable
def projection_affine : ℝ³ →ᵃ[ℝ] ℝ² :=
  {toFun := dropz, linear := sorry, map_vadd':= sorry }

noncomputable
def rotation_affine (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ³ := (Matrix.mulVecLin rot).toAffineMap

/-- Translating is affine. -/
noncomputable
def offset_affine (off : E 2) : ℝ² →ᵃ[ℝ] ℝ² :=
  {toFun v := off + v, linear := LinearMap.id, map_vadd' p v := add_vadd_comm v off p }

noncomputable
def projection_rotation_is_affine (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ² :=
  AffineMap.comp projection_affine (rotation_affine rot)

noncomputable
def offset_transform_is_affine (off : E 2) (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ² :=
  AffineMap.comp (offset_affine off) (projection_rotation_is_affine rot)

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
   apply (AffineMap.image_convexHull (offset_transform_is_affine offset ⟨inner_rot, inner_so3⟩))
 have outer_lemma : convexHull ℝ raw_outer_shadow = outer_shadow := by
   dsimp only [raw_outer_shadow, outer_shadow, hull]
   symm; rw [Set.range_comp' (fun p ↦ dropz (outer_rot *ᵥ p)) v]
   apply (AffineMap.image_convexHull (projection_rotation_is_affine ⟨outer_rot, outer_so3⟩))

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
   apply (AffineMap.image_convexHull (offset_transform_is_affine offset ⟨inner_rot, inner_so3⟩))
 have outer_lemma : convexHull ℝ raw_outer_shadow = outer_shadow := by
   dsimp only [raw_outer_shadow, outer_shadow, hull]
   symm; rw [Set.range_comp' (fun p ↦ dropz (outer_rot *ᵥ p)) v]
   apply (AffineMap.image_convexHull (projection_rotation_is_affine ⟨outer_rot, outer_so3⟩))

 change raw_inner_shadow ⊆ interior (convexHull ℝ raw_outer_shadow)
 change inner_shadow ⊆ interior outer_shadow at rupert
 rw [outer_lemma]
 rw [← inner_lemma] at rupert
 intro x hx
 exact rupert (subset_convexHull ℝ raw_inner_shadow hx)
