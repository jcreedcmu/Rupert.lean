import Mathlib

/-- The Rupert Property holds for
    - a pair of subsets X, Y of an arbitrary finite-dimensional
      real vector space P
    - a linear subspace Q of P
    if there exist
    - affine isometries transforming X and Y respectively
    such that the orthogonal projection onto Q of the transformed image of X fits
    "comfortably" within the projection onto Q of the transformed image of Y.

    By "comfortably" we mean the closure of one set is a subset of the
    interior of the other. This definition rules out trivial cases of
    a set fitting inside itself. -/
def IsLinearRupertPairForSubspace {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (X Y : Set P) (Q : Submodule ℝ P) [Nonempty Q] : Prop :=
    ∃ (Xi Yi : P →ᵃⁱ[ℝ] P),
    let Xs := (Q.orthogonalProjection ∘ Xi) '' X
    let Ys := (Q.orthogonalProjection ∘ Yi) '' Y
    closure Xs ⊆ interior Ys

/-- A pair of subsets X, Y are Rupert if there exists a coatomic subspace Q ⊆ P,
    satisfying the above definition. -/
def IsLinearRupertPair {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (X Y : Set P) : Prop :=
    ∃ (Q : Submodule ℝ P) (_ : Nonempty Q) (_ : IsCoatom Q),
    IsLinearRupertPairForSubspace X Y Q

/-- A single subset X is Rupert if the pair X, X is Rupert -/
def IsLinearRupertSet {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (X : Set P) : Prop :=
    IsLinearRupertPair X X
