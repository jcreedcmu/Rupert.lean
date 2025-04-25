import Rupert.Basic
import Rupert.Convex
import Rupert.Quaternion

namespace TriakisTetrahedron

noncomputable def triakis_tetrahedron : Fin 8 → ℝ³ := ![
  ![ 3/5,  3/5,  3/5],
  ![ 3/5, -3/5, -3/5],
  ![-3/5,  3/5, -3/5],
  ![-3/5, -3/5,  3/5],
  ![-1,  1,  1],
  ![ 1, -1,  1],
  ![ 1,  1, -1],
  ![-1, -1, -1]]

def outer_quat : Quaternion ℝ :=
  ⟨0.8587321100653562,-0.1489128073077984,-0.3524365162017292,-0.340870416742198⟩

noncomputable def outer_rot := matrix_of_quat outer_quat

lemma outer_rot_so3 : outer_rot ∈ SO3 := by
  have h : outer_quat.normSq ≠ 0 := by norm_num [outer_quat, Quaternion.normSq_def]
  exact matrix_of_quat_is_s03 h

def inner_quat : Quaternion ℝ :=
  ⟨0.1448739241252477,0.3657476586011647,-0.8546928795123707,-0.3387333435715623⟩

noncomputable def inner_rot := matrix_of_quat inner_quat

lemma inner_rot_so3 : inner_rot ∈ SO3 := by
  have h : inner_quat.normSq ≠ 0 := by norm_num [inner_quat, Quaternion.normSq_def]
  exact matrix_of_quat_is_s03 h

def inner_offset : ℝ² := ![0.0001427157746018538,0.0001489787507531265]

proof_wanted rupert : IsRupert triakis_tetrahedron
