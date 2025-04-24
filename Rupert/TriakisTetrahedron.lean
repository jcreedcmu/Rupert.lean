import Rupert.Basic
import Rupert.Convex
import Rupert.Quaternion

namespace TriakisTetrahedron

noncomputable def triakis_tetrahedron : Fin 8 → ℝ³ := ![
  ![ 3/5,  3/5,  3/5],
  ![ 3/5, -3/5, -3/5],
  ![-3/5,  3/5, -3/5],
  ![-3/5, -3/5,  3/5],
  ![-1,  1,  1],
  ![ 1, -1,  1],
  ![ 1,  1, -1],
  ![-1, -1, -1]]

def outer_quat : Quaternion ℝ :=
  ⟨0.8587321100653562,-0.1489128073077984,-0.3524365162017292,-0.340870416742198⟩

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

def inner_quat : Quaternion ℝ :=
  ⟨0.1448739241252477,0.3657476586011647,-0.8546928795123707,-0.3387333435715623⟩

noncomputable def inner_rot := matrix_of_quat inner_quat

lemma inner_rot_so3 : inner_rot ∈ SO3 := by
  have orthogonal : inner_rot ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    dsimp only [inner_rot, matrix_of_quat, inner_quat]
    norm_num1
    constructor
    · ext i j
      fin_cases i, j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j; fin_cases i, j <;> norm_num [Matrix.vecMul]
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨orthogonal, ?_⟩
  dsimp only [inner_rot, matrix_of_quat, inner_quat]
  norm_num1
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_three, Fin.succAbove]
  norm_num

def inner_offset : ℝ² := ![0.0001427157746018538,0.0001489787507531265]

proof_wanted rupert : IsRupert triakis_tetrahedron
