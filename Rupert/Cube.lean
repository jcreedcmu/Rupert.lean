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

section rotations
open Real

-- Rotate by just enough about the y-axis to bring (1, 0, √2/2) to (0, 0, z) for some z.
-- Take cos⁻¹ to find out the angle.
def outer_rot2 : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  sorry

-- Rotate 45° by x-axis
noncomputable
def outer_rot1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
 let q : Quaternion ℝ := ⟨cos (π/4), sin (π/4), 0, 0⟩
 let qnz : q.normSq ≠ 0 := by
   rw [Quaternion.normSq_def']
   simp only [cos_pi_div_four, sin_pi_div_four, ne_eq, OfNat.ofNat_ne_zero,
     not_false_eq_true, zero_pow, add_zero, add_self_eq_zero, pow_eq_zero_iff, div_eq_zero_iff,
     Nat.ofNat_nonneg, sqrt_eq_zero, or_self, q]
 let M := matrix_of_quat q
 ⟨M, matrix_of_quat_is_s03 q qnz⟩

noncomputable
def outer_rot := outer_rot2 * outer_rot1

end rotations

proof_wanted rupert : IsRupert cube
