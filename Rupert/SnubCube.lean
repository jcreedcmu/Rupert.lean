import Rupert.Basic

namespace SnubCube

noncomputable abbrev cbrt (x : ℝ) : ℝ := x ^ (1/3 : ℝ)

/-- tribonacci constant-/
noncomputable def trib : ℝ :=
  (1 + cbrt (19 + 3 * √33) + cbrt (19 - 3 * √33) ) / 3

def snub_cube : Set ℝ³ :=
  { ![      -1,  1/trib,    trib],
    ![       1, -1/trib,    trib],
    ![       1,  1/trib,   -trib],
    ![      -1, -1/trib,   -trib],

    ![ -1/trib,    trib,       1],
    ![  1/trib,   -trib,       1],
    ![  1/trib,    trib,      -1],
    ![ -1/trib,   -trib,      -1],

    ![   -trib,       1,  1/trib],
    ![    trib,      -1,  1/trib],
    ![    trib,       1, -1/trib],
    ![   -trib,      -1, -1/trib],

    ![       1,   -trib, -1/trib],
    ![      -1,    trib, -1/trib],
    ![      -1,   -trib,  1/trib],
    ![      -1,    trib,  1/trib],

    ![  1/trib,      -1,   -trib],
    ![ -1/trib,       1,   -trib],
    ![ -1/trib,      -1,    trib],
    ![  1/trib,       1,    trib],

    ![     trib, -1/trib,     -1],
    ![    -trib,  1/trib,     -1],
    ![    -trib, -1/trib,      1],
    ![     trib,  1/trib,      1]
  }

proof_wanted rupert : ¬ IsRupert snub_cube
