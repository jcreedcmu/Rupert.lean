import Rupert.Basic
import Rupert.Convex
import Rupert.Quaternion

namespace Tetrahedron

def tetrahedron : Fin 4 → ℝ³ := ![
  ![ 1,  1,  1],
  ![ 1, -1, -1],
  ![-1,  1, -1],
  ![-1, -1,  1]]

def outer_quat : Quaternion ℝ :=
  ⟨0.3389904789675945, -0.4261829733457893, 0.1736023394555525, -0.8205581978964213⟩

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
  ⟨0.8577016212029301, -0.1191615236085398, 0.4439711748359327, 0.2302999265999848⟩

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

def inner_offset : ℝ² := ![0.09841265604345877,-0.165800542996898]

theorem rupert : IsRupert tetrahedron := by
  use outer_rot, outer_rot_so3, inner_rot, inner_rot_so3, inner_offset
  intro outer_shadow inner_shadow
  let ε₀ : ℝ := 0.001
  have hε₀ : ε₀ ∈ Set.Ioo 0 1 := by norm_num
  have hb : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer_shadow := by
    refine ball_in_hull_of_corners_in_hull hε₀ ?_ ?_ ?_ ?_
    · sorry
    · sorry
    · sorry
    · sorry
  intro v hv
  let ε₁ : ℝ := 0.00001
  have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num
  refine mem_interior_hull hε₀.1 hε₁ hb ?_
  simp only [Set.mem_range, inner_shadow] at hv
  obtain ⟨y, hy⟩ := hv
  fin_cases y <;>
    simp only [tetrahedron, Fin.reduceFinMk, Matrix.cons_val, inner_shadow] at hy
  · sorry
  · sorry
  · sorry
  · sorry
