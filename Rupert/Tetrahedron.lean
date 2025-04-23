import Rupert.Basic
import Rupert.Convex

namespace Tetrahedron

def tetrahedron : Set ℝ³ :=
  { ![1, 1, 0],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1]
  }

structure Quaternion (R : Type) : Type where
  x : R
  y : R
  z : R
  w : R

def outer_quat : Quaternion ℝ :=
  ⟨0.47272822265830911,0.1073127286952434,
   0.71778574787387106,0.49979575724832803⟩

def matrix_of_quat {R : Type} [Field R] (q : Quaternion R)
    : Matrix (Fin 3) (Fin 3) R :=
  let ⟨x,y,z,w⟩ := q
  let normsq := w^2 + x^2 + y^2 + z^2
  !![(w^2  + x^2 - y^2 - z^2) / normsq,
       2 * (x * y + z * w) / normsq,
       2 * (z * x - y * w) / normsq;
     2 * (x * y - z * w) / normsq,
       (w^2 - x^2 + y^2 - z^2) / normsq,
       2 * (y * z + x * w) / normsq;
     2 * (z * x + y * w) / normsq,
       2 * (y * z - x * w) / normsq,
       (w^2 - x^2 - y^2 + z^2) / normsq;]

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
