import Rupert.Basic

namespace Cube

def cube : Set ℝ³ :=
  { ![ 1,  1,  1],
    ![ 1, -1,  1],
    ![-1, -1,  1],
    ![-1,  1,  1],
    ![ 1,  1, -1],
    ![ 1, -1, -1],
    ![-1, -1, -1],
    ![-1,  1, -1]
  }

theorem rupert : IsRupert cube := by
  sorry
