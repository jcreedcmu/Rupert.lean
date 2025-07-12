import Mathlib
import Rupert.Basic
import Rupert.LinearRupert

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P] (X Y : Set P)

-- #check exists_orthonormalBasis
-- #check LinearEquiv.ofRankEq
-- #check Orthonormal.exists_orthonormalBasis_extension_of_card_eq
-- #check Submodule.Quotient.nontrivial_of_lt_top


theorem foo (Q : Submodule ℝ P) (Qcoatom : IsCoatom Q) : False := by
 let nQ : ℕ := Module.finrank ℝ Q
 -- a basis for the subspace Q
 have bQ : Basis (Fin nQ) ℝ Q := Module.finBasis ℝ Q
 -- it can be construed as a function to Q
 let bQf : Fin nQ → Q := bQ
 -- ...which is an independent set
 have bQf_ind : LinearIndependent ℝ bQf := Basis.linearIndependent bQ
 -- it's also a function to the ambient space P
 let bQf2 : Fin nQ → P := Q.subtype ∘ bQf
 -- I'd like to conclude that bQf2 is LinearIndependent
 let bQf2 : LinearIndependent ℝ bQf2 := by
    exact LinearIndependent.map' bQf_ind Q.subtype (Submodule.ker_subtype Q)


 sorry


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

  let bQf : Fin nQ → P := Q.subtype ∘ bQ
  let bQf' : Option (Fin nQ) → P := fun i => i.casesOn' x bQf

  have bQ_ind : LinearIndependent ℝ bQ := Basis.linearIndependent bQ
  let bQf_ind : LinearIndependent ℝ bQf :=
    LinearIndependent.map' bQ_ind Q.subtype (Submodule.ker_subtype Q)
  have x_not_in_bQf : x ∉ Submodule.span ℝ (Set.range bQf) := sorry

  have h : Submodule.span ℝ (Set.range (Q.subtype ∘ bQ)) = Q.carrier := by
    ext
    sorry
  have bQf'_ind := bQf_ind.option x_not_in_bQf

  sorry

  -- let extended : Fin (nQ + 1) → P := Fin.cases x (fun i => bQ i)
  -- have extended_ind : LinearIndependent ℝ extended := sorry
  -- sorry
#exit


  let Q' := Submodule.span ℝ (Set.range extended)

  have Q_le_Q' : Q < Q' := by
    change Q.carrier ⊂ Q'.carrier

    sorry


  have : Module.finrank ℝ Q' = Module.finrank ℝ P := by
   rw [show Q' = (⊤ : Submodule ℝ P) from Qmax Q' Q_le_Q']
   exact finrank_top ℝ P

  let m : Module.finrank ℝ Q' = Cardinal.mk (Set.range extended) := (Submodule.finrank_eq_rank ℝ P Q').trans (rank_span extended_ind)
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
