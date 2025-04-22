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

proof_wanted rupert : IsRupert cube
