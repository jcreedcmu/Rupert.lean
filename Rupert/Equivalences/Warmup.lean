import Mathlib
import Rupert.Basic

noncomputable
def kernel_proj_subspace {I : Type} [Fintype I] [DecidableEq I] (i : I) : Submodule ℝ (EuclideanSpace ℝ I) :=
 LinearMap.ker (LinearMap.proj i)

noncomputable
def kernel_proj {I : Type} [Fintype I] [DecidableEq I] (i : I) (v : EuclideanSpace ℝ I) : EuclideanSpace ℝ I :=
 fun j ↦ if i = j then 0 else v j

theorem kernel_proj_subspace_def {I : Type} [Fintype I] [DecidableEq I] {i : I} (u : EuclideanSpace ℝ I)
    (h : u ∈ kernel_proj_subspace i) : u i = 0 := h

theorem orthogonal_proj_eq_zeroing_map {I : Type} [Fintype I] [DecidableEq I] (i : I) (v : EuclideanSpace ℝ I) :
  (kernel_proj_subspace i).orthogonalProjection v = kernel_proj i v := by
    let v1 (j : I) := if i = j then 0 else v j
    let v2 (j : I) := if i = j then v j else 0

    -- The vector v is equal to the sum of v1, a component in the
    -- subspace, and v2, a component in the orthogonal complement.
    have split : v = v1 + v2 := by
      ext j; dsimp [v1, v2]
      match decEq i j with
      | isTrue h => simp [← h]
      | isFalse h => simp [if_neg h]
    let proj := (kernel_proj_subspace i).orthogonalProjection

    -- In fact v1 is in the subspace:
    have hk1 : proj v1 = v1 := by
     apply (Submodule.orthogonalProjection_eq_self_iff (K := kernel_proj_subspace i)).mpr
     dsimp [kernel_proj_subspace]
     simp only [LinearMap.mem_ker]
     change LinearMap.proj i v1 = 0
     simp [v1]

    -- In fact v2 is in the orthogonal complement of the subspace:
    have hk2 : proj v2 = 0 := by
     rw [Submodule.orthogonalProjection_eq_zero_iff, Submodule.mem_orthogonal]
     intro u a
     dsimp [inner]
     simp only [conj_trivial]
     apply Fintype.sum_eq_zero; intro j
     match decEq i j with
      | isTrue h => rw [← h, kernel_proj_subspace_def u a]; simp
      | isFalse h => simp [v2, if_neg h]

    rw [split, proj.map_add]
    change (proj v1 + proj v2) = fun j ↦ if i = j then 0 else (v1 + v2) j
    rw [hk1, hk2]; dsimp [v1, v2]; ext j
    match decEq i j with
     | isTrue h => simp only [← h, ↓reduceIte, add_zero]
     | isFalse h => simp only [if_neg h, add_zero]

theorem orthogonal_proj_r2_def' (x : ℝ³) : (kernel_proj_subspace 2).orthogonalProjection x = ![x 0, x 1, 0] := by
 rw [orthogonal_proj_eq_zeroing_map 2]
 ext i; fin_cases i <;> dsimp [kernel_proj]
