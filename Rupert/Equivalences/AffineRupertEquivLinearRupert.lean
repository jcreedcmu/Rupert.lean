import Mathlib
import Rupert.Basic
import Rupert.AffineRupert
import Rupert.LinearRupert
import Rupert.Equivalences.ProjectionLemmas
open Matrix

-- Thanks to Jireh Loreaux!
-- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Orthogonal.20projection.20commutes.20with.20affine.20space.20inclusion/with/527494321
theorem affine_projection_eq_linear_projection {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (Q : Submodule ℝ P) [Nonempty Q] (p : P) :
  Q.orthogonalProjection p = EuclideanGeometry.orthogonalProjection Q.toAffineSubspace p := by
    ext1
    apply Set.eq_of_mem_singleton
    rw [← EuclideanGeometry.inter_eq_singleton_orthogonalProjection]
    apply Set.mem_inter (by simp)
    simp only [Submodule.toAffineSubspace_direction, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub]
    rw [← neg_mem_iff, neg_sub]
    simp

theorem linear_for_subspace_imp_affine_for_subspace {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] [FiniteDimensional ℝ P] (X Y : Set P)
    (Q : Submodule ℝ P) [Nonempty Q] :
    IsLinearRupertPairForSubspace X Y Q → IsAffineRupertPairForSubspace X Y (Q.toAffineSubspace) := by
    intro ⟨ Xi, Yi, hsub ⟩
    use Xi.toAffineIsometry, Yi.toAffineIsometry
    let aproj := EuclideanGeometry.orthogonalProjection Q.toAffineSubspace

    have Xe : Q.orthogonalProjection ∘ Xi = aproj ∘ Xi := by
     ext1 p; change Q.orthogonalProjection (Xi p) = aproj (Xi p)
     rw [affine_projection_eq_linear_projection Q (Xi p)]

    have Ye : Q.orthogonalProjection ∘ Yi = aproj ∘ Yi := by
     ext1 p; change Q.orthogonalProjection (Yi p) = aproj (Yi p)
     rw [affine_projection_eq_linear_projection Q (Yi p)]

    change closure ((aproj ∘ Xi) '' X) ⊆ interior ((aproj ∘ Yi) '' Y)
    rw [← Xe, ← Ye]
    exact hsub
