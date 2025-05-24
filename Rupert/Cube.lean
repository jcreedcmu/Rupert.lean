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

proof_wanted rupert : IsRupert cube
