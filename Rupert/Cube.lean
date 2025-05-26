import Rupert.Basic
import Rupert.Convex
import Rupert.Quaternion


namespace Cube

def cube : Fin 8 → ℝ³ := ![
  ![ 1,  1,  1],
  ![ 1, -1,  1],
  ![-1, -1,  1],
  ![-1,  1,  1],
  ![ 1,  1, -1],
  ![ 1, -1, -1],
  ![-1, -1, -1],
  ![-1,  1, -1]]

noncomputable
abbrev outer_rot_denorm : Matrix (Fin 3) (Fin 3) ℝ :=
   !![ 0,  2, √2;
     -√3, -1, √2;
      √3, -1, √2]

noncomputable
abbrev outer_rot : Matrix (Fin 3) (Fin 3) ℝ :=
   (1/√6) • outer_rot_denorm

private
lemma outer_rot_o3_lemma1 : (star outer_rot_denorm) * outer_rot_denorm = 6 • 1:= by
  (ext i j; fin_cases i, j) <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul])
  all_goals norm_num
  all_goals ring_nf

private
lemma outer_rot_o3_lemma2 : (outer_rot_denorm) * (star outer_rot_denorm) = 6 • 1:= by
  (ext i j; fin_cases i, j) <;> (simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul])
  all_goals norm_num

lemma outer_rot_so3 : outer_rot ∈ SO3 := by
 have h : (6 : ℝ) • 1 = (6 : Matrix (Fin 3) (Fin 3) ℝ) :=
   Matrix.smul_one_eq_diagonal 6
 have h2: (√6)⁻¹ * (√6)⁻¹ * 6 = 1 := by field_simp
 let r := (√6)⁻¹
 have hr : (√6)⁻¹ = r := rfl
 dsimp only [outer_rot]
 rw [Matrix.mem_specialOrthogonalGroup_iff]
 constructor
 · constructor
   · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, outer_rot_o3_lemma1, smul_smul]
     simp only [one_div, star_trivial, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
     rw [← h, smul_smul, h2, one_smul]
   · rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, outer_rot_o3_lemma2, smul_smul]
     simp only [one_div, star_trivial, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
     rw [← h, smul_smul, h2, one_smul]
 · have : (Fin.succAbove 2 1 : Fin 3) = 1 := by rfl
   simp only [one_div, Matrix.smul_of, Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty,
     mul_neg, mul_one, Matrix.det_succ_row_zero, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
     Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
     Matrix.submatrix_apply, Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.submatrix_submatrix,
     Matrix.det_unique, Fin.default_eq_zero, Function.comp_apply, Fin.succ_one_eq_two,
     Matrix.cons_val, Fin.sum_univ_two, Fin.val_zero, pow_zero, one_mul, Fin.zero_succAbove,
     Fin.val_one, pow_one, neg_mul, ne_eq, one_ne_zero, not_false_eq_true,
     Fin.succAbove_ne_zero_zero, Fin.sum_univ_three, neg_neg, zero_mul, Fin.one_succAbove_one,
     zero_add, Fin.val_two, even_two, Even.neg_pow, one_pow, Fin.reduceEq]
   simp_all only [Matrix.cons_val]
   ring_nf
   suffices h : (r * r * 6) * (√3 * √2) * r = 1 by (ring_nf at h; exact h)
   simp_all only [h2]
   rw [show √3 * √2 = √6 by calc √3 * √2
     _ = √(3 * 2) := by exact Eq.symm (Real.sqrt_mul' 3 (show 0 ≤ 2 by positivity))
     _ = √6 := by norm_num]
   change 1 * √6 * (√6)⁻¹ = 1
   field_simp

proof_wanted rupert : IsRupert cube
