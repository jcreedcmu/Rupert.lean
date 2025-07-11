import Mathlib

/-- The Rupert Property holds for
    - a pair of subsets X, Y of an arbitrary finite-dimensional Euclidean space P
    - a nonempty linear subspace Q of P
    if there exist
    - affine isometries transforming X and Y respectively
    such that the orthogonal projection onto Q of the transformed image of X fits
    "comfortably" within the projection onto Q of the transformed image of Y.

    By "comfortably" we mean the closure of one set is a subset of the
    interior of the other. This definition rules out trivial cases of
    a set fitting inside itself. -/
def IsEuclideanRupertPairForSubspace {I : Type*} [Fintype I]
    (X Y : Set (EuclideanSpace ℝ I)) (Q : Submodule ℝ (EuclideanSpace ℝ I)) [Nonempty Q] : Prop :=
    ∃ (Xi Yi : (EuclideanSpace ℝ I) →ᵃⁱ[ℝ] (EuclideanSpace ℝ I)),
    let Xs := (Q.orthogonalProjection ∘ Xi) '' X
    let Ys := (Q.orthogonalProjection ∘ Yi) '' Y
    closure Xs ⊆ interior Ys

/-- A pair of subsets X, Y are Rupert if there exists a coatomic subspace Q ⊆ P,
    satisfying the above definition. -/
def IsEuclideanRupertPair {I : Type*} [Fintype I] (X Y : Set (EuclideanSpace ℝ I)) : Prop :=
    ∃ (Q : Submodule ℝ (EuclideanSpace ℝ I)) (_ : Nonempty Q) (_ : IsCoatom Q),
    IsEuclideanRupertPairForSubspace X Y Q

/-- A chosen subspace ℝⁿ ⊆ ℝⁿ⁺¹. It maps (x₁, …, xₙ) to (x₁, …, xₙ, 0) --/
noncomputable
def canonical_subspace (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  LinearMap.ker (LinearMap.proj (Fin.last n))

/-- A pair of subsets X, Y are Rupert if they are rupert with respect to the canonical
    linear subspace of one dimension less. -/
def IsEuclideanRupertPair' {n : ℕ} (X Y : Set (EuclideanSpace ℝ (Fin (n + 1)))) : Prop :=
    IsEuclideanRupertPairForSubspace X Y (canonical_subspace n)

/-- A single subset X is Rupert if the pair X, X is Rupert -/
def IsEuclideanRupertSet {I : Type*} [Fintype I] (X : Set (EuclideanSpace ℝ I)) : Prop :=
    IsEuclideanRupertPair X X
