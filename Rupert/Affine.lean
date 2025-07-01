import Mathlib
import Rupert.Basic

open scoped Matrix

/-- The Rupert Property for a pair of subsets X, Y of an arbitrary
    affine space. X has the Rupert property with respect to Y if there
    exist affine isometries transforming X and Y respectively such
    that the shadow of X transformed fits "comfortably" within the
    shadow of Y transformed, after being projected to a maximal
    nontrivial affine subspace. transformations.

    By "comfortably" we mean the closure of one set is a subset of the
    interior of the other. This definition rules out trivial cases of
    a set fitting inside itself. -/
def IsAffineRupertPair {P : Type*} {V : Type*} [MetricSpace P] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddTorsor V P]
    (inner outer : Set P) : Prop :=
    ∃ (inner_isometry outer_isometry : AffineIsometry ℝ P P)
      (Q : AffineSubspace ℝ P) (_ : Nonempty Q) (_ : IsCoatom Q)
      (_ : Q.direction.HasOrthogonalProjection), -- I don't want to depend on this as an argument
    let proj := EuclideanGeometry.orthogonalProjection (V := V) (P := P) Q
    let inner_shadow := (proj ∘ inner_isometry) '' inner
    let outer_shadow: Set Q := (proj ∘ outer_isometry) '' outer
    closure inner_shadow ⊆ interior outer_shadow

/-- The Rupert Property for a subset S of affine space P. S has the Rupert property
    if it has the pairwise Rupert property with respect to itself. -/
def IsAffineRupertSet  {P : Type*} {V : Type*} [MetricSpace P] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddTorsor V P]
    (S : Set P) : Prop :=
    IsAffineRupertPair S S
