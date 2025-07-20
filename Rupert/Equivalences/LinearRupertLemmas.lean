import Mathlib
import Rupert.Basic
import Rupert.LinearRupert

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

-- FIXME: is there a better way?
lemma not_top_implies_not_univ {Q : Submodule ℝ P} (Qnontriv : ¬Q = ⊤) :
    Q.carrier ≠ Set.univ :=
  fun a =>
     False.elim (Qnontriv (Submodule.ext fun x ↦ Eq.to_iff (congrFun a x)))


variable [FiniteDimensional ℝ P] (X Y : Set P)


-- FIXME: is there a better way?
lemma in_basis_span_imp_in_submodule (Q : Submodule ℝ P) (x : P) :
    x ∈ Submodule.span ℝ (Set.range (Q.subtype ∘ Module.finBasis ℝ Q)) → x ∈ Q.carrier := by
 rw [Set.range_comp, Submodule.span_image]
 simp only [Basis.span_eq, Submodule.map_top, Submodule.range_subtype, Submodule.carrier_eq_coe,
   SetLike.mem_coe, imp_self]


theorem coatomic_subspace_dim (Q : Submodule ℝ P) (Qcoatom : IsCoatom Q) :
    Module.finrank ℝ P = Module.finrank ℝ Q + 1 := by
  simp_all [IsCoatom]
  obtain ⟨Qnontriv, Qmax⟩ := Qcoatom

  have hne : Q.carrier ≠ Set.univ := not_top_implies_not_univ Qnontriv

  -- x an element in P \ Q
  let ⟨ x, hx ⟩ := (Set.ne_univ_iff_exists_notMem Q.carrier).mp hne
  let n : ℕ := Module.finrank ℝ P
  let nQ : ℕ := Module.finrank ℝ Q

  let bP : Basis (Fin n) ℝ P := Module.finBasis ℝ P
  let bQ : Basis (Fin nQ) ℝ Q := Module.finBasis ℝ Q

  let bQf : Fin nQ → P := Q.subtype ∘ bQ
  let bQf' : Option (Fin nQ) → P := fun i => i.casesOn' x bQf

  have bQ_ind : LinearIndependent ℝ bQ := Basis.linearIndependent bQ
  have bQf_ind : LinearIndependent ℝ bQf :=
    LinearIndependent.map' bQ_ind Q.subtype (Submodule.ker_subtype Q)
  have x_not_in_bQf : x ∉ Submodule.span ℝ (Set.range bQf) := by
    intro hhx
    refine False.elim (hx ?_)
    apply in_basis_span_imp_in_submodule
    exact hhx

  have bQf'_spans : ⊤ ≤ Submodule.span ℝ (Set.range bQf') := by
    refine eq_top_iff.mp ?_
    refine Qmax (Submodule.span ℝ (Set.range bQf')) ?_

    constructor
    · intro q qh
      have : q ∈ Set.range bQf' := sorry
      simp only [Submodule.span, Submodule.sInf_coe, Set.mem_iInter]
      exact fun _ j ↦ j this

    · sorry


  have bQf'_ind := bQf_ind.option x_not_in_bQf

  have bQf'_basis : Basis (Option (Fin nQ)) ℝ P := Basis.mk bQf'_ind bQf'_spans

  have P_rank : Module.finrank ℝ P = Nat.card (Option (Fin nQ)) :=
    Module.finrank_eq_nat_card_basis bQf'_basis

  rw [P_rank, Finite.card_option, Nat.card_fin]


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
