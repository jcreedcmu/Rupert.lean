import Mathlib
import Rupert.Basic
import Rupert.LinearRupert
import Rupert.EuclideanRupert
open Matrix

theorem euclidean_for_subspace_imp_linear_for_subspace {I : Type*} [Fintype I]
    (X Y : Set (EuclideanSpace ℝ I)) (Q : Submodule ℝ (EuclideanSpace ℝ I)) [Nonempty Q] :
    IsEuclideanRupertPairForSubspace X Y Q → IsLinearRupertPairForSubspace X Y Q := by
  intro ⟨Xi, Yi, hsub⟩
  use Xi, Yi

theorem linear_for_subspace_imp_euclidean_for_subspace {I : Type*} [Fintype I]
    (X Y : Set (EuclideanSpace ℝ I)) (Q : Submodule ℝ (EuclideanSpace ℝ I)) [Nonempty Q] :
    IsLinearRupertPairForSubspace X Y Q → IsEuclideanRupertPairForSubspace X Y Q := by
  intro ⟨Xi, Yi, hsub⟩
  use Xi, Yi

theorem linear_for_subspace_iff_euclidean_for_subspace {I : Type*} [Fintype I]
    (X Y : Set (EuclideanSpace ℝ I)) (Q : Submodule ℝ (EuclideanSpace ℝ I)) [Nonempty Q] :
    IsLinearRupertPairForSubspace X Y Q ↔ IsEuclideanRupertPairForSubspace X Y Q :=
   ⟨ linear_for_subspace_imp_euclidean_for_subspace _ _ _,
     euclidean_for_subspace_imp_linear_for_subspace _ _ _⟩
