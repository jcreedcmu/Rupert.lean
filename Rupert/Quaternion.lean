import Mathlib

def matrix_of_quat {R : Type} [Field R] (q : Quaternion R)
    : Matrix (Fin 3) (Fin 3) R :=
  let ⟨w, x, y, z⟩ := q
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
