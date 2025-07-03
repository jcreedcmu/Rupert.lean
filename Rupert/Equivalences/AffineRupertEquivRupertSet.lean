import Mathlib
import Rupert.Basic
import Rupert.Set
import Rupert.Affine
open Matrix


set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
set_option pp.showLetValues false

noncomputable
def so3_to_affine_isometry (rot : SO3) : AffineIsometry ℝ ℝ³ ℝ³ := by
 let ⟨ mat, rot_so3 ⟩ := rot
 refine ⟨?_, ?_⟩
 · refine {toFun := mat.mulVec, linear := mat.mulVecLin, map_vadd' := ?_}
   sorry
 · sorry

def inject (v : ℝ²) : ℝ³ := ![v 0, v 1, 0]

noncomputable
-- It is more helpful to define this in terms of Fin n → ℝ instead of ℝⁿ
-- For some reason ℝ² prevents Matrix.toLin'_apply from unifying
def injectl : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' !![1, 0; 0, 1; 0, 0]

noncomputable
def projectl : ℝ³ →ₗ[ℝ] ℝ² := Matrix.toLin' !![1, 0, 0; 0, 1, 0]



-- set_option pp.all true

noncomputable
def translation_to_affine_isometry (trans : ℝ³) : AffineIsometry ℝ ℝ³ ℝ³ := by
 refine ⟨?_, ?_⟩
 · refine {toFun v := v + trans, linear := LinearMap.id, map_vadd' := ?_}
   sorry
 · sorry

-- FIXME: what's the right theorem to capture something like:
-- If A and A' are isomorphic as vector spaces, and A' ⊆ B as affine spaces
-- then A and A' are isomorphic as affine spaces?
theorem subspace_helper (A B : Type)  : True := sorry

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

    have linear_derived_map (p2 : ℝ²) : R2as :=
      ⟨ injectl p2, by
        rw [injectl, toLin'_apply]
        simp_all only [cons_mulVec, cons_dotProduct, zero_mul, dotProduct_empty, add_zero]
        rfl
        ⟩

    let lincl : ℝ² ≃ᵃⁱ[ℝ] R2as := AffineIsometryEquiv.mk' linear_derived_map sorry ![0,0]  sorry

    let incl2 : ℝ² ≃ₜ R2as := lincl.toHomeomorph

    -- Inclusion map from ℝ² into the subspace R2as
    -- Will need to show it commutes with projection or something
    let incl : ℝ² ≃ₜ R2as := {
      -- FIXME: If I call inject p2 here, it breaks proofs. Why?
      toFun p2 := ⟨ ![p2 0, p2 1, 0], rfl ⟩
      invFun pas := let p3 : ℝ³ := pas; ![p3 0, p3 1]
      left_inv := by
        intros x; ext i; fin_cases i <;> simp
      right_inv := by
        intros x; ext i; fin_cases i
        · simp
        · simp
        · simp only [Fin.reduceFinMk, Matrix.cons_val]
          rw [x.property]
      continuous_toFun := by sorry
      continuous_invFun := by sorry
    }

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
