import Mathlib
import Rupert.Basic
import Rupert.Set
import Rupert.Affine
import Rupert.Equivalences.ProjectionLemmas
open Matrix

-- set_option pp.deepTerms true
-- set_option pp.proofs true
-- set_option pp.maxSteps 1000000
-- set_option pp.showLetValues false

noncomputable
def Matrix.UnitaryGroup.toLinearIsometryEquiv
    {n : Type*} [DecidableEq n] [Fintype n]
    (k : Type*) [RCLike k]
    (M : unitaryGroup n k) : EuclideanSpace k n ≃ₗᵢ[k] EuclideanSpace k n :=
  let matrix_to_endomorphism := unitary.map (F := Matrix n n k ≃⋆ₐ[k] (EuclideanSpace k n →L[k] EuclideanSpace k n))
    Matrix.toEuclideanCLM
  unitary.linearIsometryEquiv (matrix_to_endomorphism M)

noncomputable
def so3_to_affine_isometry (rot : SO3) : ℝ³ →ᵃⁱ[ℝ] ℝ³ :=
  let u := Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup rot
  (Matrix.UnitaryGroup.toLinearIsometryEquiv ℝ u).toAffineIsometryEquiv.toAffineIsometry

def inject (v : ℝ²) : ℝ³ := ![v 0, v 1, 0]

noncomputable
-- It is more helpful to define this in terms of Fin n → ℝ instead of ℝⁿ
-- For some reason ℝ² prevents Matrix.toLin'_apply from unifying
def injectl : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' !![1, 0; 0, 1; 0, 0]

noncomputable
def projectl : ℝ³ →ₗ[ℝ] ℝ² := Matrix.toLin' !![1, 0, 0; 0, 1, 0]

theorem proj_offset_commute (q : ℝ³) (offset : ℝ²) : offset + proj_xy q = proj_xy (inject offset + q) := by
  ext i;  fin_cases i <;> simp [proj_xy, inject]

theorem R2_coatom : IsCoatom R2as := sorry

noncomputable
def injectl_subspace (p2 : ℝ²) : ↑ R2as := ⟨ injectl p2, his p2 ⟩ where
    his (p2 : ℝ²) : injectl p2 ∈ R2as := by
        rw [injectl, toLin'_apply]
        simp_all only [cons_mulVec, cons_dotProduct, zero_mul, dotProduct_empty, add_zero]
        rfl

theorem affine_rupert_pair_imp_rupert_set_pair (X Y : Set ℝ³) :
    IsAffineRupertPair X Y → IsRupertPair X Y := by sorry

theorem rupert_set_pair_imp_affine_rupert_set_pair (X Y : Set ℝ³) :
    IsRupertPair X Y → IsAffineRupertPair X Y := by
    intro ⟨inner_rot, inner_so3, inner_offset, outer_rot, outer_so3, hcontain⟩
    let inner_shadow := {x | ∃ p ∈ X, inner_offset + proj_xy (inner_rot.mulVec p) = x};
    let outer_shadow := {x | ∃ p ∈ Y, proj_xy (outer_rot.mulVec p) = x};
    change closure inner_shadow ⊆ interior outer_shadow at hcontain
    let inner_offset_isom : ℝ³ →ᵃⁱ[ℝ] ℝ³ := (AffineIsometryEquiv.constVAdd ℝ ℝ³ (inject inner_offset)).toAffineIsometry
    let inner_rot_isom : ℝ³ →ᵃⁱ[ℝ] ℝ³ := so3_to_affine_isometry ⟨ inner_rot, inner_so3 ⟩
    let outer_rot_isom : ℝ³ →ᵃⁱ[ℝ] ℝ³ := so3_to_affine_isometry ⟨ outer_rot, outer_so3 ⟩
    use inner_offset_isom.comp inner_rot_isom, outer_rot_isom, R2as, inferInstance, R2_coatom

    let inner_shadow' := (affine_oproj ∘ (inner_offset_isom.comp inner_rot_isom)) '' X
    let outer_shadow' := (affine_oproj ∘ outer_rot_isom) '' Y;
    change closure inner_shadow' ⊆ interior outer_shadow'

    let lincl : ℝ² ≃ᵃⁱ[ℝ] R2as := AffineIsometryEquiv.mk' injectl_subspace sorry ![0,0]  sorry

    let incl : ℝ² ≃ₜ R2as := lincl.toHomeomorph

    have proj_eq_inject_comp_proj (w : ℝ³) : affine_oproj w = injectl_subspace (proj_xy w) := by
      apply Subtype.val_inj.mp
      change affine_oproj w = injectl (proj_xy w)
      rw [affine_oproj_eq_eproj_r2]
      ext i; fin_cases i <;> simp [eproj, injectl, proj_xy]

    have hinner : inner_shadow' = incl '' inner_shadow := by
      change (affine_oproj ∘ (inner_offset_isom.comp inner_rot_isom)) '' X =
           incl '' ((λ p ↦ inner_offset + proj_xy (inner_rot.mulVec p)) '' X)
      rw [← Set.image_comp]
      have h2 : ∀ x : ℝ³, affine_oproj (inner_offset_isom.comp inner_rot_isom x)
                        = incl (inner_offset + proj_xy (inner_rot *ᵥ x)) := by
          intro x
          rw [proj_offset_commute]
          let inj_inner_offset : Fin 3 → ℝ := inject inner_offset
          exact proj_eq_inject_comp_proj (inj_inner_offset + inner_rot *ᵥ x)

      have h : affine_oproj ∘ (inner_offset_isom.comp inner_rot_isom) = (incl ∘ fun p ↦ inner_offset + proj_xy (inner_rot *ᵥ p)) := by
        ext x i; apply congrFun; simp only [SetLike.coe_eq_coe]; apply h2
      rw[h]

    have houter : outer_shadow' = incl '' outer_shadow := by
      change (affine_oproj ∘ outer_rot_isom) '' Y =
           incl '' ((λ p ↦  proj_xy (outer_rot.mulVec p)) '' Y)
      rw [← Set.image_comp]
      have h2 : ∀ x : ℝ³, affine_oproj (outer_rot_isom x)
                        = incl (proj_xy (outer_rot *ᵥ x)) :=
          λ x ↦ proj_eq_inject_comp_proj (outer_rot *ᵥ x)

      have h : affine_oproj ∘ outer_rot_isom = (incl ∘ fun p ↦ proj_xy (outer_rot *ᵥ p)) := by
        ext x i; apply congrFun; simp only [SetLike.coe_eq_coe]; apply h2
      rw[h]

    rw [hinner, houter]
    rw [← Homeomorph.image_closure incl inner_shadow, ← Homeomorph.image_interior incl outer_shadow]
    exact Set.image_mono hcontain

theorem affine_rupert_pair_iff_rupert_set_pair (X Y : Set ℝ³) :
    IsAffineRupertPair X Y ↔ IsRupertPair X Y := by
  exact { mp := affine_rupert_pair_imp_rupert_set_pair X Y,
          mpr:= rupert_set_pair_imp_affine_rupert_set_pair X Y }

theorem affine_rupert_iff_rupert_set (X : Set (EuclideanSpace ℝ (Fin 3))) :
    IsAffineRupertSet X ↔ IsRupertSet X := affine_rupert_pair_iff_rupert_set_pair X X
