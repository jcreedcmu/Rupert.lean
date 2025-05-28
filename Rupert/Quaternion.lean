import Mathlib
import Rupert.Basic

/-- Converts a quaternion to a normalized rotation matrix. -/
def matrix_of_quat {R : Type} [Field R] (q : Quaternion R)
    : Matrix (Fin 3) (Fin 3) R :=
  let ⟨w, x, y, z⟩ := q
  let normsq := w^2 + x^2 + y^2 + z^2
  !![(w^2  + x^2 - y^2 - z^2) / normsq,
       2 * (x * y - z * w) / normsq,
       2 * (z * x + y * w) / normsq;
     2 * (x * y + z * w) / normsq,
       (w^2 - x^2 + y^2 - z^2) / normsq,
       2 * (y * z - x * w) / normsq;
     2 * (z * x - y * w) / normsq,
       2 * (y * z + x * w) / normsq,
       (w^2 - x^2 - y^2 + z^2) / normsq;]

/-- A version of converting quaternions to matrices without
   normalization, under the assumption that it might be easier to
   reason about it postponing the divisions until later. -/
def denorm_matrix_of_quat {R : Type} [Field R] (q : Quaternion R)
    : Matrix (Fin 3) (Fin 3) R :=
  let ⟨w, x, y, z⟩ := q
  !![(w^2  + x^2 - y^2 - z^2) ,
       2 * (x * y - z * w),
       2 * (z * x + y * w);
     2 * (x * y + z * w),
       (w^2 - x^2 + y^2 - z^2),
       2 * (y * z - x * w);
     2 * (z * x - y * w),
       2 * (y * z + x * w),
       (w^2 - x^2 - y^2 + z^2);]

def normalized_denorm_is_matrix {R : Type} [Field R] (q : Quaternion R) :
    let ⟨w, x, y, z⟩ := q
    let normsq := w^2 + x^2 + y^2 + z^2
    matrix_of_quat q = (1 / normsq) • denorm_matrix_of_quat q := by
  dsimp only [matrix_of_quat, denorm_matrix_of_quat]
  ext i j; fin_cases i, j;
  all_goals (simp only [one_div]; apply div_eq_inv_mul)

/- Here are a couple of lemmas showing that the unnormalized version of the quaternion matrix,
   when multiplied by its own transpose in either order, is the norm of q to the fourth power. -/

lemma denorm_half_unitary (q : Quaternion ℝ)
   : (denorm_matrix_of_quat q) * star (denorm_matrix_of_quat q) = (Quaternion.normSq q)^2 • 1 := by
  let ⟨r,x,y,z⟩ := q; ext i j; fin_cases i, j
  all_goals simp only [denorm_matrix_of_quat, Matrix.mul_apply, Fin.sum_univ_succ, Quaternion.normSq];
  all_goals simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
   Matrix.cons_val_fin_one, star_trivial, Fin.succ_zero_eq_one, Matrix.cons_val_one,
   Fin.succ_one_eq_two, Matrix.cons_val, Finset.univ_eq_empty, Matrix.cons_val_succ, Finset.sum_const, Finset.card_empty,
   zero_smul, add_zero, Quaternion.mul_re, Quaternion.star_re, Quaternion.star_imI, mul_neg, sub_neg_eq_add,
   Quaternion.star_imJ, Quaternion.star_imK, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Matrix.smul_apply,
   Matrix.one_apply_eq, smul_eq_mul]
  all_goals (simp; ring_nf)

lemma denorm_half_unitary2 (q : Quaternion ℝ)
   : star (denorm_matrix_of_quat q) * (denorm_matrix_of_quat q) = (Quaternion.normSq q)^2 • 1 := by
  let ⟨r,x,y,z⟩ := q; ext i j; fin_cases i, j
  all_goals simp only [denorm_matrix_of_quat, Matrix.mul_apply, Fin.sum_univ_succ, Quaternion.normSq];
  all_goals simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
   Matrix.cons_val_fin_one, star_trivial, Fin.succ_zero_eq_one, Matrix.cons_val_one,
   Fin.succ_one_eq_two, Matrix.cons_val, Finset.univ_eq_empty, Matrix.cons_val_succ, Finset.sum_const, Finset.card_empty,
   zero_smul, add_zero, Quaternion.mul_re, Quaternion.star_re, Quaternion.star_imI, mul_neg, sub_neg_eq_add,
   Quaternion.star_imJ, Quaternion.star_imK, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Matrix.smul_apply,
   Matrix.one_apply_eq, smul_eq_mul]
  all_goals (simp; ring_nf)

lemma matrix_of_quat_is_unitary (q : Quaternion ℝ) (nz : Quaternion.normSq q ≠ 0)
   : matrix_of_quat q ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
 rw [normalized_denorm_is_matrix q]
 let n2 := (1 / (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2))
 have local_arith : n2 * n2 * (Quaternion.normSq q)^2 = 1 := by
       change n2 * n2 * Quaternion.normSq q ^ 2 = 1
       simp only [n2 ]
       rw [← Quaternion.normSq_def', sq, mul_mul_mul_comm]
       simp_all only [ne_eq, one_div, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel,
         mul_one]
 constructor
 · rw[star_smul, smul_mul_smul_comm, denorm_half_unitary2, smul_smul, show star n2 = n2 by rfl, local_arith]
   apply one_smul
 · rw[star_smul, smul_mul_smul_comm, denorm_half_unitary, smul_smul, show star n2 = n2 by rfl, local_arith]
   apply one_smul

lemma denorm_matrix_of_quat_has_correct_det (q : Quaternion ℝ)
   : (denorm_matrix_of_quat q).det = (Quaternion.normSq q)^3 := by
 let ⟨r, x, y, z⟩ := q
 simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, denorm_matrix_of_quat, Quaternion.normSq_def'];
 simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.val_zero, pow_zero,
   Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, one_mul,
   Fin.succAbove_zero, Matrix.submatrix_apply, Fin.succ_zero_eq_one, Matrix.cons_val_one,
   Fin.val_eq_zero, Fin.succ_one_eq_two, Matrix.cons_val, Matrix.submatrix_submatrix,
   Matrix.submatrix_empty, Matrix.det_fin_zero, Finset.univ_eq_empty, Matrix.cons_val_succ,
   Finset.sum_const, Finset.card_empty, smul_add, zero_smul, add_zero, Fin.val_one, pow_one,
   neg_mul, Fin.succAbove, Fin.castSucc_zero, Fin.lt_one_iff, ↓reduceIte, Fin.castSucc_eq_zero_iff,
   Finset.sum_empty, Fin.val_succ, zero_add, Fin.succ_pos, Fin.castSucc_lt_succ_iff,
   le_of_subsingleton, Finset.sum_neg_distrib, neg_zero, Fin.castSucc_one, lt_self_iff_false,
   Fin.val_two, even_two, Even.neg_pow, one_pow, Fin.reduceLT, neg_sub]
 ring_nf

lemma matrix_of_quat_has_det_one (q : Quaternion ℝ) (nz : Quaternion.normSq q ≠ 0)
   : (matrix_of_quat q).det = 1 := by
 rw [normalized_denorm_is_matrix q]
 let n2 := (1 / (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2))
 rw [Matrix.det_smul, denorm_matrix_of_quat_has_correct_det]
 change n2 ^ 3 * Quaternion.normSq q ^ 3 = 1
 simp_all only [← mul_pow, one_div, ← Quaternion.normSq_def',
                isUnit_iff_ne_zero, ne_eq, not_false_eq_true,
                IsUnit.inv_mul_cancel, one_pow, n2]

theorem matrix_of_quat_is_s03 {q : Quaternion ℝ} (nz : Quaternion.normSq q ≠ 0) : matrix_of_quat q ∈ SO3 :=
  ⟨ matrix_of_quat_is_unitary q nz,
    matrix_of_quat_has_det_one q nz ⟩

/- Some lemmas about specific rotations -/
section Rotations
open Real
open Matrix

noncomputable
def rotate_x_quat (θ : ℝ) : Quaternion ℝ :=
   ⟨cos (θ/2), sin (θ/2), 0, 0⟩

noncomputable
def rotate_x_mat (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
   !![1,       0,        0;
      0, cos (θ), -sin (θ);
      0, sin (θ),  cos (θ) ]


theorem rotate_x (θ : ℝ) : matrix_of_quat (rotate_x_quat θ) = rotate_x_mat θ := by
  simp only [rotate_x_quat, matrix_of_quat, rotate_x_mat]
  have arith : 2 * (θ / 2) = θ := by
    rw [← mul_div_assoc, mul_comm, mul_div_cancel_of_invertible]
  ext i j; fin_cases i, j
  all_goals simp only [cos_sq_add_sin_sq, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow,
    sub_zero, add_zero, mul_zero, zero_mul, div_one,
    of_apply, Fin.reduceFinMk, cons_val]
  · rw [← cos_two_mul', arith];
  · rw [zero_sub, mul_neg,  ← mul_assoc, ← sin_two_mul, arith]
  · rw [zero_add, ← mul_assoc, ← sin_two_mul, arith]
  · rw [← cos_two_mul', arith];


def rotateAux (c s : ℝ) (v : ℝ³) : Quaternion ℝ :=
   ⟨c, s * v 0, s * v 1, s * v 2⟩

theorem rotate_aux_normal (c s : ℝ) (v : ℝ³)
      (h1 : c ^ 2 + s ^ 2 = 1) (h2 : ‖v‖ ^ 2 = 1) :
      matrix_of_quat (rotateAux c s v) = denorm_matrix_of_quat (rotateAux c s v) := by
  have alg : (c ^ 2 + (s * v 0) ^ 2 + (s * v 1) ^ 2 + (s * v 2) ^ 2) = 1 := by
     ring_nf
     have : c ^ 2 + s ^ 2 * v 0 ^ 2 + s ^ 2 * v 1 ^ 2 + s ^ 2 * v 2 ^ 2 =
            c ^ 2 + s ^ 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
            ring_nf
     rw[this]
     have sqnorm : ‖v‖^2 = (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
       rw [← real_inner_self_eq_norm_sq ]
       simp_all only  [inner, Fin.sum_univ_succ]
       simp only [ RCLike.inner_apply, conj_trivial, Fin.succ_zero_eq_one,
         Fin.succ_one_eq_two]
       ring_nf
     rw [← sqnorm, h2]
     ring_nf
     exact h1

  ext i j
  simp [matrix_of_quat, denorm_matrix_of_quat, rotateAux, alg]

/- Given a pair of vectors src, tgt, return a rotation that rotates src
   to be parallel to tgt -/
noncomputable
def rotateToTarget (src tgt : ℝ³) : Quaternion ℝ :=
   let θ := cos⁻¹ (inner ℝ src tgt / (2 * ‖src‖ * ‖tgt‖))
   let v := src ×₃ tgt
   ⟨cos (θ/2), sin (θ/2) * v 0, sin (θ/2) * v 1, sin (θ/2) * v 2⟩

theorem rotate_parallel_target (src tgt : ℝ³) : ∃ ℓ : ℝ,
        matrix_of_quat (rotateToTarget src tgt) *ᵥ src = ℓ • tgt := by
  use ?wit
  · let θ := cos⁻¹ (inner ℝ src tgt / (2 * ‖src‖  * ‖tgt‖))
    let v := src ×₃ tgt
    simp only [matrix_of_quat]
    rw [show rotateToTarget src tgt = ⟨cos (θ/2), sin (θ/2) * v 0, sin (θ/2) * v 1, sin (θ/2) * v 2⟩ by rfl]
    dsimp only;
    ext i; fin_cases i;
    · beta_reduce; simp only [Matrix.mulVec];
      dsimp only [Fin.isValue, Fin.zero_eta, of_apply, cons_val_zero, PiLp.smul_apply, smul_eq_mul];
      dsimp only [dotProduct]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      simp only [Fin.isValue, cons_val_zero, Fin.succ_zero_eq_one, cons_val_one,
        Fin.succ_one_eq_two, cons_val, add_zero]
      dsimp only [v, crossProduct]; simp;
      sorry
    · sorry
    · sorry
  sorry
end Rotations
