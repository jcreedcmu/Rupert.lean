import Rupert.Quaternion

def normalized_denorm_is_matrix {R : Type} [Field R] (q : Quaternion R) :
    let ⟨w, x, y, z⟩ := q
    let normsq := w^2 + x^2 + y^2 + z^2
    matrix_of_quat q = (1 / normsq) • denorm_matrix_of_quat q := by
  ext i j; fin_cases i, j; all_goals simp; all_goals sorry
