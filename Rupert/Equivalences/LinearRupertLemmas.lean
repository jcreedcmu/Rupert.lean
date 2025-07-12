import Mathlib
import Rupert.Basic
import Rupert.LinearRupert

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P] (X Y : Set P)

-- #check exists_orthonormalBasis
-- #check LinearEquiv.ofRankEq
-- #check Orthonormal.exists_orthonormalBasis_extension_of_card_eq
-- #check Submodule.Quotient.nontrivial_of_lt_top


theorem coatomic_subspace_dim (Q : Submodule ℝ P) (Qcoatom : IsCoatom Q) :
    Module.finrank ℝ P = Module.finrank ℝ Q + 1 := by
  simp_all [IsCoatom]
  obtain ⟨Qnontriv, Qmax⟩ := Qcoatom

  -- FIXME: is there a better way?
  have hne : Q.carrier ≠ Set.univ := fun a =>
     False.elim (Qnontriv (Submodule.ext fun x ↦ Eq.to_iff (congrFun a x)))

  -- x an element in P \ Q
  let ⟨ x, hx ⟩ := (Set.ne_univ_iff_exists_notMem Q.carrier).mp hne
  let n : ℕ := Module.finrank ℝ P
  let nQ : ℕ := Module.finrank ℝ Q

  have bP : Basis (Fin n) ℝ P := Module.finBasis ℝ P
  have bQ : Basis (Fin nQ) ℝ Q := Module.finBasis ℝ Q

  let extended : Fin (nQ + 1) → P := Fin.cases x (fun i => bQ i)

  let Q' := Submodule.span ℝ (Set.range extended)

  have Q_le_Q' : Q < Q' := sorry

  have : Module.finrank ℝ Q' = Module.finrank ℝ P := by
   rw [show Q' = (⊤ : Submodule ℝ P) from Qmax Q' Q_le_Q']
   exact finrank_top ℝ P


  sorry


theorem coatomic_subspaces_equivalent (Q1 Q2 : Submodule ℝ P) (_ : IsCoatom Q1) (_ : IsCoatom Q2) :
    ∃ T : P ≃ₗᵢ[ℝ] P, Submodule.map T Q1 = Q2 := by
  sorry

section nonempty_q
variable (Q : Submodule ℝ P) [Nonempty Q]

theorem linear_rupert_respects_subspace_iso (T : P ≃ₗᵢ[ℝ] P) :
    IsLinearRupertPairForSubspace X Y Q → IsLinearRupertPairForSubspace X Y (Submodule.map T Q) := by
  sorry

theorem linear_rupert_pair_imp_subspace (Qcoatom : IsCoatom Q) :
    IsLinearRupertPair X Y → IsLinearRupertPairForSubspace X Y Q := by
  intro ⟨ Q', Q'inh, Q'coatom, hrup ⟩
  let ⟨ T, hT ⟩ := coatomic_subspaces_equivalent Q' Q Q'coatom Qcoatom
  simp only [← hT]
  exact linear_rupert_respects_subspace_iso X Y Q' T hrup

theorem linear_rupert_pair_iff_subspace (Qcoatom : IsCoatom Q) :
    IsLinearRupertPair X Y ↔ IsLinearRupertPairForSubspace X Y Q :=
  ⟨ linear_rupert_pair_imp_subspace X Y Q Qcoatom,
    fun rup => ⟨ Q, inferInstance, Qcoatom, rup ⟩⟩
end nonempty_q
