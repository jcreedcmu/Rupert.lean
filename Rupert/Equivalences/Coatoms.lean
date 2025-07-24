import Mathlib

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

-- FIXME: is there a better way?
lemma not_top_implies_not_univ {Q : Submodule ℝ P} (Qnontriv : ¬Q = ⊤) :
    Q.carrier ≠ Set.univ :=
  fun a =>
     False.elim (Qnontriv (Submodule.ext fun x ↦ Eq.to_iff (congrFun a x)))

def vector_outside_submodule (Q : Submodule ℝ P) (Qcoatom : IsCoatom Q) : ∃ x : P, x ∉ Q :=
  (Set.ne_univ_iff_exists_notMem Q.carrier).mp (not_top_implies_not_univ Qcoatom.1)



theorem coatom_linear_subspaces_equiv (Q1 Q2 : Submodule ℝ P) (_ : IsCoatom Q1) (_ : IsCoatom Q2) :
    ∃ T : P ≃ₗᵢ[ℝ] P, Submodule.map T Q1 = Q2 := by

  obtain ⟨s1, ⟨b1⟩⟩ := Basis.exists_basis ℝ Q1
  obtain ⟨s2, ⟨b2⟩⟩ := Basis.exists_basis ℝ Q2

  sorry
