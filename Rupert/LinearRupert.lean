import Mathlib

/-- The Rupert Property for a pair of subsets X, Y of an arbitrary
    finite-dimensional real vector space P with chosen subspace Q. X
    has the Rupert property with respect to Y and the maximal nonempty
    subspace Q if there exist - linear isometries transforming X and Y
    respectively such that the orthogonal projection onto Q of the
    transformed image of X fits "comfortably" within the projection
    onto Q of the transformed image of Y.

    By "comfortably" we mean the closure of one set is a subset of the
    interior of the other. This definition rules out trivial cases of
    a set fitting inside itself. -/
def IsLinearRupertPairForSubspace {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (inner outer : Set P) (Q : Submodule ℝ P) [Nonempty Q] (_ : IsCoatom Q) : Prop :=
    ∃ (inner_isometry outer_isometry : P →ₗᵢ[ℝ] P),
    let proj := Submodule.orthogonalProjection Q
    let inner_shadow : Set Q := (proj ∘ inner_isometry : P → Q) '' inner
    let outer_shadow : Set Q := (proj ∘ outer_isometry : P → Q) '' outer
    closure inner_shadow ⊆ interior outer_shadow

/-- A pair of subsets X, Y are Rupert if there exists a subspace satisfying
    the above definition. -/
def IsLinearRupertPair {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (inner outer : Set P) : Prop :=
    ∃ (Q : Submodule ℝ P) (_ : Nonempty Q) (Qca : IsCoatom Q),
    IsLinearRupertPairForSubspace inner outer Q Qca

/-- A single subset X is Rupert if the pair X, X is Rupert -/
def IsLinearRupertSet {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (X : Set P) : Prop :=
    IsLinearRupertPair X X
