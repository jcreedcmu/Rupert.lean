import Rupert.Basic

namespace Tetrahedron

def tetrahedron : Set ℝ³ :=
  { ![1, 1, 0],
    ![1, -1, -1],
    ![-1, 1, -1],
    ![-1, -1, 1]
  }

theorem rupert : IsRupert tetrahedron := by
  sorry
