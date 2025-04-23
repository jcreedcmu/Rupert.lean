import Rupert.Basic
import Rupert.Convex
import Rupert.Quaternion

namespace Tetrahedron

def tetrahedron : Set ℝ³ :=
  { ![1, 1, 0],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1]
  }

def outer_quat : Quaternion ℝ :=
  ⟨0.49979575724832803, 0.47272822265830911, 0.1073127286952434, 0.71778574787387106⟩

noncomputable def outer_rot := matrix_of_quat outer_quat

lemma outer_rot_so3 : outer_rot ∈ SO3 := by
  have orthogonal : outer_rot ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    dsimp only [outer_rot, matrix_of_quat, outer_quat]
    norm_num1
    constructor
    · ext i j
      fin_cases i, j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j; fin_cases i, j <;> norm_num [Matrix.vecMul]
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨orthogonal, ?_⟩
  dsimp only [outer_rot, matrix_of_quat, outer_quat]
  norm_num1
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_three, Fin.succAbove]
  norm_num

proof_wanted rupert : IsRupert tetrahedron
