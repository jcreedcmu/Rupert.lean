import Mathlib
import Rupert.Basic

/--
 - The point of this file is to establish that the projection from ℝⁿ
 - onto ℝⁿ⁻¹ behaves as expected, and specifically we use this for n =
 - 3.
 --/

-- The linear subspace corresponding to the kernel of the ith projection ℝⁿ → ℝ
noncomputable
def proj_subspace {I : Type} [Fintype I] [DecidableEq I] (i : I) : Submodule ℝ (EuclideanSpace ℝ I) :=
 LinearMap.ker (LinearMap.proj i)

-- The canonical affine subspace corresponding to the kernel of the ith projection ℝⁿ → ℝ
noncomputable
def proj_affine_subspace {I : Type} [Fintype I] [DecidableEq I] (i : I) : AffineSubspace ℝ (EuclideanSpace ℝ I) :=
   (proj_subspace i).toAffineSubspace

-- An explicit definition of the projection
noncomputable
def eproj {I : Type} [Fintype I] [DecidableEq I] (i : I) (v : EuclideanSpace ℝ I) : EuclideanSpace ℝ I :=
 fun j ↦ if i = j then 0 else v j

-- Nonemptiness of a linear subspace is inherited by the corresponding affine subspace
-- FIXME: should this be in mathlib already?
instance {k : Type*} {V : Type*} [Ring k] [AddCommGroup V] [Module k V] (p : Submodule k V)
  : Nonempty p.toAffineSubspace :=
  ⟨0, by simp⟩

theorem affine_projection_eq_linear_projection_euclidean
  {I : Type} [Fintype I] (s : Submodule ℝ (EuclideanSpace ℝ I))
  [Nonempty s] (v : EuclideanSpace ℝ I) :
  EuclideanGeometry.orthogonalProjection s.toAffineSubspace v = s.orthogonalProjection v := by
    let s1 : EuclideanSpace ℝ I →ᵃ[ℝ] s.toAffineSubspace := EuclideanGeometry.orthogonalProjection s.toAffineSubspace
    let s2 : EuclideanSpace ℝ I →ᵃ[ℝ] s := s.orthogonalProjection.toAffineMap

    let z : (EuclideanGeometry.orthogonalProjection s.toAffineSubspace).linear = s.toAffineSubspace.direction.orthogonalProjection := by
     apply EuclideanGeometry.orthogonalProjection_linear

    -- have h : s1 = s2 := by
    --   apply AffineMap.ext_linear
    --   sorry
    change s1 v = s2 v
    sorry

theorem proj_subspace_def {I : Type} [Fintype I] [DecidableEq I] {i : I} (u : EuclideanSpace ℝ I)
    (h : u ∈ proj_subspace i) : u i = 0 := h

theorem oproj_eq_eproj {I : Type} [Fintype I] [DecidableEq I] (i : I) (v : EuclideanSpace ℝ I) :
  (proj_subspace i).orthogonalProjection v = eproj i v := by
    let v1 (j : I) := if i = j then 0 else v j
    let v2 (j : I) := if i = j then v j else 0

    -- The vector v is equal to the sum of v1, a component in the
    -- subspace, and v2, a component in the orthogonal complement.
    have split : v = v1 + v2 := by
      ext j; dsimp [v1, v2]
      match decEq i j with
      | isTrue h => simp [← h]
      | isFalse h => simp [if_neg h]
    let oproj := (proj_subspace i).orthogonalProjection

    -- In fact v1 is in the subspace:
    have hk1 : oproj v1 = v1 := by
     apply (Submodule.orthogonalProjection_eq_self_iff (K := proj_subspace i)).mpr
     dsimp [proj_subspace]
     simp only [LinearMap.mem_ker]
     change LinearMap.proj i v1 = 0
     simp [v1]

    -- In fact v2 is in the orthogonal complement of the subspace:
    have hk2 : oproj v2 = 0 := by
     rw [Submodule.orthogonalProjection_eq_zero_iff, Submodule.mem_orthogonal]
     intro u a
     dsimp [inner]
     simp only [conj_trivial]
     apply Fintype.sum_eq_zero; intro j
     match decEq i j with
      | isTrue h => rw [← h, proj_subspace_def u a]; simp
      | isFalse h => simp [v2, if_neg h]

    rw [split, oproj.map_add]
    change (oproj v1 + oproj v2) = fun j ↦ if i = j then 0 else (v1 + v2) j
    rw [hk1, hk2]; dsimp [v1, v2]; ext j
    match decEq i j with
     | isTrue h => simp only [← h, ↓reduceIte, add_zero]
     | isFalse h => simp only [if_neg h, add_zero]

theorem oproj_eq_eproj_r2 (x : ℝ³) : (proj_subspace 2).orthogonalProjection x = ![x 0, x 1, 0] := by
 rw [oproj_eq_eproj 2]
 ext i; fin_cases i <;> dsimp [eproj]

theorem affine_oproj_eq_eproj_r2 (x : ℝ³) :
  EuclideanGeometry.orthogonalProjection (P := ℝ³) ((proj_subspace 2).toAffineSubspace) x = ![x 0, x 1, 0] := by
 rw [affine_projection_eq_linear_projection_euclidean]
 apply oproj_eq_eproj_r2
