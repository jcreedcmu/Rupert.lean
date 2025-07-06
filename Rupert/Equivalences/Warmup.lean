import Mathlib
import Rupert.Basic

/--
 - Projecting the Z coordinate from ℝ³.
 --/
noncomputable
def projZ : ℝ³ →ₗ[ℝ] ℝ := LinearMap.proj 2

/--
 - ℝ² as a linear subspace of ℝ³. It's the kernel of projecting the Z coordinate.
 --/
noncomputable
def xyplane := LinearMap.ker projZ

/--
 - The orthogonal projection onto the XY-plane is the function that sets Z to zero.
 --/
theorem orthogonal_proj_r2_def' (x : ℝ³) : xyplane.orthogonalProjection x = ![x 0, x 1, 0] := by
  let v1 := ![x 0, x 1, 0]
  let v2 := ![0, 0, x 2]
  have split : x = v1 + v2 := by dsimp[v1, v2]; ext i; fin_cases i <;> simp
  let proj := xyplane.orthogonalProjection

  have hk1 : proj v1 = v1 := by
    apply (Submodule.orthogonalProjection_eq_self_iff (K := xyplane)).mpr
    apply LinearMap.proj_apply

  have hk2 : proj v2 = 0 := by
    rw [Submodule.orthogonalProjection_eq_zero_iff, Submodule.mem_orthogonal]
    intro u a
    dsimp [inner]
    simp only [conj_trivial, Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one,
               Fin.succ_one_eq_two, Finset.univ_eq_empty,
               Finset.sum_empty, add_zero]
    simp [show v2 0 = 0 by dsimp[v2], show v2 1 = 0 by dsimp[v2], show u 2 = 0 from a]
  rw [split, proj.map_add]
  change proj v1 + proj v2 = ![(v1 + v2) 0, (v1 + v2) 1, 0]
  rw [hk1, hk2]; dsimp [v1, v2]; ext i; fin_cases i <;> simp
