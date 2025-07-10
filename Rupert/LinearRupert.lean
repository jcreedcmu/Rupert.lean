import Mathlib

/-- The Rupert Property for a pair of subsets X, Y of an arbitrary
    finite-dimensional real vector space P. X has the Rupert property
    with respect to Y if there exist
    - linear isometries transforming X and Y respectively
    - an maximal nontrivial linear subspace Q of P
    such that the orthogonal projection onto Q of the transformed image of X fits
    "comfortably" within the projection onto Q of the transformed image of Y.

    By "comfortably" we mean the closure of one set is a subset of the
    interior of the other. This definition rules out trivial cases of
    a set fitting inside itself. -/
def IsLinearRupertPair {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (inner outer : Set P) : Prop :=
    ∃ (inner_isometry outer_isometry : P →ₗᵢ[ℝ] P)
      (Q : Submodule ℝ P) (_ : Nonempty Q) (_ : IsCoatom Q),
    let proj := Submodule.orthogonalProjection Q
    let inner_shadow : Set Q := (proj ∘ inner_isometry : P → Q) '' inner
    let outer_shadow : Set Q := (proj ∘ outer_isometry : P → Q) '' outer
    closure inner_shadow ⊆ interior outer_shadow

/-- The Rupert Property for a subset S of linear space P. S has the Rupert property
    if it has the pairwise Rupert property with respect to itself. -/
def IsLinearRupertSet {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (S : Set P) : Prop :=
    IsLinearRupertPair S S
