import Mathlib

/-- The Rupert Property holds for
    - a pair of subsets X, Y of an arbitrary finite-dimensional
      real affine space P
    - an affine subspace Q of P
    if there exist
    - affine isometries transforming X and Y respectively
    such that the orthogonal projection onto Q of the transformed image of X fits
    "comfortably" within the projection onto Q of the transformed image of Y.

    By "comfortably" we mean the closure of one set is a subset of the
    interior of the other. This definition rules out trivial cases of
    a set fitting inside itself. -/
def IsAffineRupertPairForSubspace {P : Type*} {V : Type*} [MetricSpace P] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
    (X Y : Set P) (Q : AffineSubspace ℝ P) [Nonempty Q] : Prop :=
    ∃ (Xi Yi : P →ᵃⁱ[ℝ] P),
    let proj := EuclideanGeometry.orthogonalProjection Q
    let Xs := (proj ∘ Xi) '' X
    let Ys := (proj ∘ Yi) '' Y
    closure Xs ⊆ interior Ys

/-- A pair of subsets X, Y are Rupert if there exists a coatomic subspace Q ⊆ V,
    satisfying the above definition. -/
def IsAffineRupertPair {P : Type*} {V : Type*} [MetricSpace P] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
    (X Y : Set P) : Prop :=
    ∃ (Q : AffineSubspace ℝ P) (_ : Nonempty Q) (_ : IsCoatom Q),
    IsAffineRupertPairForSubspace X Y Q

/-- A single subset X is Rupert if the pair X, X is Rupert -/
def IsAffineRupertSet  {P : Type*} {V : Type*} [MetricSpace P] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddTorsor V P] [FiniteDimensional ℝ V]
    (X : Set P) : Prop :=
    IsAffineRupertPair X X
