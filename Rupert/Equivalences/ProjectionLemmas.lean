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

-- Thanks to Jireh Loreaux!
-- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Orthogonal.20projection.20commutes.20with.20affine.20space.20inclusion/with/527494321
theorem affine_projection_eq_linear_projection_euclidean
  {I : Type} [Fintype I] (s : Submodule ℝ (EuclideanSpace ℝ I))
  [Nonempty s] (v : EuclideanSpace ℝ I) :
  EuclideanGeometry.orthogonalProjection s.toAffineSubspace v = s.orthogonalProjection v := by
    symm
    ext1
    apply Set.eq_of_mem_singleton
    rw [← EuclideanGeometry.inter_eq_singleton_orthogonalProjection]
    apply Set.mem_inter (by simp)
    simp only [Submodule.toAffineSubspace_direction, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub]
    rw [← neg_mem_iff, neg_sub]
    simp

theorem proj_subspace_def {I : Type} [Fintype I] [DecidableEq I] {i : I} (u : EuclideanSpace ℝ I)
    (h : u ∈ proj_subspace i) : u i = 0 := h

theorem oproj_eq_eproj {I : Type} [Fintype I] [DecidableEq I] (i : I) (v : EuclideanSpace ℝ I) :
  (proj_subspace i).orthogonalProjection v = eproj i v := by
    with_reducible let v1 (j : I) := if i = j then 0 else v j
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

theorem oproj_eq_eproj_r2 (x : ℝ³) : (proj_subspace 2).orthogonalProjection x = eproj 2 x := by
 rw [oproj_eq_eproj 2]

@[reducible] noncomputable
def R2as : AffineSubspace ℝ ℝ³ := (proj_subspace 2).toAffineSubspace

@[reducible] noncomputable
def R2ss : Submodule ℝ ℝ³ := proj_subspace 2

@[reducible] noncomputable
def affine_oproj : ℝ³ →ᵃ[ℝ] R2as := EuclideanGeometry.orthogonalProjection R2as

theorem affine_oproj_eq_eproj_r2 (x : ℝ³) : affine_oproj x = eproj 2 x := by
 dsimp only [ContinuousAffineMap.coe_toAffineMap]
 rw [affine_projection_eq_linear_projection_euclidean]
 apply oproj_eq_eproj_r2

def proj_kernel_basis {I : Type} [Fintype I] [DecidableEq I] (i : I) :
    Basis {j : I // j ≠ i} ℝ (proj_subspace i) :=
  sorry

noncomputable
def linear_subspace_has_dim_one_less {I : Type} [Fintype I] [DecidableEq I] (i : I) :
  ↥(proj_subspace i) ≃ₗᵢ[ℝ] EuclideanSpace ℝ { j // j ≠ i } := by
  let J := {j : I // j ≠ i}
  have lineq : proj_subspace i ≃ₗ[ℝ] EuclideanSpace ℝ J :=
    (proj_kernel_basis i).repr.trans (Finsupp.linearEquivFunOnFinite ℝ ℝ J)
  have pres_norm : ∀ (x : proj_subspace i), ‖lineq x‖ = ‖x‖ := sorry
  exact LinearIsometryEquiv.mk lineq pres_norm

noncomputable
def R2_eq_proj_subspace : R2ss ≃ₗᵢ[ℝ] ℝ² := by
  have eq : { j : Fin 3 // j ≠ 2 } ≃ Fin 2 := {
    toFun x := match x with
      | ⟨0, _⟩ => 0
      | ⟨1, _⟩ => 1
      | ⟨2, hy⟩ => absurd rfl hy
    invFun x :=
     match x with
     | ⟨0, _⟩ => ⟨0, by tauto⟩
     | ⟨1, _⟩ => ⟨1, by tauto⟩
    left_inv x := by
     let ⟨y, hy⟩ := x
     fin_cases y; all_goals try simp
     tauto
    right_inv x := by fin_cases x <;> simp
  }
  exact (linear_subspace_has_dim_one_less 2).trans (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eq)


-- noncomputable
-- def R2as_eq_proj_subspace : R2as ≃ᵃⁱ[ℝ] ℝ² := R2_eq_proj_subspace.toAffineIsometryEquiv
