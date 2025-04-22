import Rupert.Basic

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

def outer_quat : Quaternion ℚ :=
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

#eval (matrix_of_quat outer_quat).transpose * (matrix_of_quat outer_quat)

theorem rupert : IsRupert tetrahedron := by
  sorry
