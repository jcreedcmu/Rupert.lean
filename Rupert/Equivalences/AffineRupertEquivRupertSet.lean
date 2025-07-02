import Mathlib
import Rupert.Basic
import Rupert.Set
import Rupert.Affine

set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
set_option pp.showLetValues true

noncomputable
def so3_to_affine_isometry (rot : SO3) : AffineIsometry ℝ ℝ³ ℝ³ := by
 let ⟨ mat, rot_so3 ⟩ := rot
 refine ⟨?_, ?_⟩
 · refine {toFun := mat.mulVec, linear := mat.mulVecLin, map_vadd' := ?_}
   sorry
 · sorry

def inject (v : ℝ²) : ℝ³ := ![v 0, v 1, 0]

noncomputable
def translation_to_affine_isometry (trans : ℝ³) : AffineIsometry ℝ ℝ³ ℝ³ := by
 refine ⟨?_, ?_⟩
 · refine {toFun v := v + trans, linear := LinearMap.id, map_vadd' := ?_}
   sorry
 · sorry

theorem affine_rupert_pair_iff_rupert_set_pair (X Y : Set ℝ³) :
    IsAffineRupertPair X Y ↔ IsRupertPair X Y := by
  have mp : IsAffineRupertPair X Y → IsRupertPair X Y := by
    sorry
  have mpr : IsRupertPair X Y → IsAffineRupertPair X Y := by
    intro ⟨inner_rot, inner_so3, inner_offset, outer_rot, outer_so3, hcontain⟩
    let inner_shadow := {x | ∃ p ∈ X, inner_offset + proj_xy (inner_rot.mulVec p) = x};
    let outer_shadow := {x | ∃ p ∈ Y, proj_xy (outer_rot.mulVec p) = x};
    change closure inner_shadow ⊆ interior outer_shadow at hcontain
    let inner_offset_isom : ℝ³ →ᵃⁱ[ℝ] ℝ³ := translation_to_affine_isometry (inject inner_offset)
    let inner_rot_isom : ℝ³ →ᵃⁱ[ℝ] ℝ³ := so3_to_affine_isometry ⟨ inner_rot, inner_so3 ⟩
    let outer_rot_isom : ℝ³ →ᵃⁱ[ℝ] ℝ³ := so3_to_affine_isometry ⟨ outer_rot, outer_so3 ⟩
    use inner_offset_isom.comp inner_rot_isom
    use outer_rot_isom
    let R2 : Set ℝ³ := { x | x 2 = 0 }
    have R2_nonempty : Nonempty R2 := Nonempty.intro ⟨ ![0,0,0], rfl ⟩
    let R2as : AffineSubspace ℝ ℝ³ := { carrier := R2, smul_vsub_vadd_mem := sorry }
    have R2_coatom : IsCoatom R2as := sorry
    use R2as, R2_nonempty, R2_coatom
    let proj := EuclideanGeometry.orthogonalProjection R2as
    let inner_shadow' := (proj ∘ (inner_offset_isom.comp inner_rot_isom)) '' X
    let outer_shadow' := (proj ∘ outer_rot_isom) '' Y;
    change closure inner_shadow' ⊆ interior outer_shadow'
    let incl : ℝ² ≃ₜ R2as := sorry -- need this commute with some stuff probably
    have hinner : inner_shadow' = incl '' inner_shadow :=
      sorry
    have houter : outer_shadow' = incl '' outer_shadow :=
      sorry
    rw [hinner, houter]
    rw [← Homeomorph.image_closure incl inner_shadow, ← Homeomorph.image_interior incl outer_shadow]
    exact Set.image_mono hcontain
  exact { mp, mpr }

theorem affine_rupert_iff_rupert_set (X : Set (EuclideanSpace ℝ (Fin 3))) :
    IsAffineRupertSet X ↔ IsRupertSet X := affine_rupert_pair_iff_rupert_set_pair X X
