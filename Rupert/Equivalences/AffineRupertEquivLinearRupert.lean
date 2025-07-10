import Mathlib
import Rupert.Basic
import Rupert.AffineRupert
import Rupert.LinearRupert
import Rupert.Equivalences.ProjectionLemmas
open Matrix


theorem linear_for_subspace_imp_affine_for_subspace {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] [FiniteDimensional ℝ P] (X Y : Set P)
    (Q : Submodule ℝ P) [Nonempty Q] :
    IsLinearRupertPairForSubspace X Y Q → IsAffineRupertPairForSubspace X Y (Q.toAffineSubspace) := by
    intro ⟨ Xi, Yi, hsub ⟩
    let Xs := (Q.orthogonalProjection ∘ Xi) '' X
    let Ys := (Q.orthogonalProjection ∘ Yi) '' Y
    change closure Xs ⊆ interior Ys at hsub
    use Xi.toAffineIsometry, Yi.toAffineIsometry
    let aproj := EuclideanGeometry.orthogonalProjection Q.toAffineSubspace
    change closure ((aproj ∘ Xi) '' X) ⊆ interior ((aproj ∘ Yi) '' Y)
    sorry
