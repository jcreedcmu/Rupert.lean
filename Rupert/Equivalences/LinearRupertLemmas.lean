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

lemma in_submodule_imp_in_basis_span (Q : Submodule ℝ P) (x : P) :
    x ∈ Q.carrier → x ∈ Submodule.span ℝ (Set.range (Q.subtype ∘ Module.finBasis ℝ Q)) := by
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
  have x_not_in_span_bQf : x ∉ Submodule.span ℝ (Set.range bQf) :=
    fun hhx => False.elim (hx (in_basis_span_imp_in_submodule Q x hhx))

  have x_in_span_bQf' : x ∈ Submodule.span ℝ (Set.range bQf') :=
    Submodule.mem_span_of_mem (Exists.intro none rfl)

  have bQf'_spans : ⊤ ≤ Submodule.span ℝ (Set.range bQf') := by
    refine eq_top_iff.mp (Qmax (Submodule.span ℝ (Set.range bQf')) ?_)
    constructor
    · intro q qh
      have range_sub : Set.range bQf ⊆ Set.range bQf' := by
        intro p ⟨ hp1, hp2 ⟩
        use some hp1
        rw [← hp2]
        rfl
      exact Submodule.span_mono range_sub (in_submodule_imp_in_basis_span Q q qh)

    · exact fun h => False.elim (hx (h x_in_span_bQf'))

  have bQf'_ind := bQf_ind.option x_not_in_span_bQf

  have bQf'_basis : Basis (Option (Fin nQ)) ℝ P := Basis.mk bQf'_ind bQf'_spans

  have P_rank : Module.finrank ℝ P = Nat.card (Option (Fin nQ)) :=
    Module.finrank_eq_nat_card_basis bQf'_basis

  rw [P_rank, Finite.card_option, Nat.card_fin]

theorem coatomic_subspaces_equivalent (Q1 Q2 : Submodule ℝ P) (_ : IsCoatom Q1) (_ : IsCoatom Q2) :
    ∃ T : P ≃ₗᵢ[ℝ] P, Submodule.map T Q1 = Q2 := by
  sorry

section nonempty_q
variable (Q : Submodule ℝ P) [Nonempty Q]

-- have Xs := ⇑(Submodule.map T Q).orthogonalProjection ∘ ⇑Xi' '' X;
lemma equiv_map_ortho {P1 P2 : Type*} [NormedAddCommGroup P1] [InnerProductSpace ℝ P1] [FiniteDimensional ℝ P1]
   [NormedAddCommGroup P2] [InnerProductSpace ℝ P2] [FiniteDimensional ℝ P2]
    (T : P1 →ₗᵢ[ℝ] P2) (Q : Submodule ℝ P1) (v : P1) :
    (Submodule.map T Q).orthogonalProjection (T v) = T (Q.orthogonalProjection v) :=
   Eq.symm (LinearIsometry.map_orthogonalProjection' T Q v)


lemma equiv_map_ortho2 {P1 P2 : Type*} [NormedAddCommGroup P1] [InnerProductSpace ℝ P1] [FiniteDimensional ℝ P1]
   [NormedAddCommGroup P2] [InnerProductSpace ℝ P2] [FiniteDimensional ℝ P2]
    (T : P1 ≃ₗᵢ[ℝ] P2) (Q : Submodule ℝ P1) (v : P1) :
     False := by
  let z1 : P1 →L[ℝ] Submodule.map T Q := ((Submodule.map T Q).orthogonalProjection).comp T.toContinuousLinearMap
  let z2 : P1 →L[ℝ] Q := Q.orthogonalProjection
  let m : P1 →L[ℝ] P2 := T.toContinuousLinearMap
  let z3 : Q →ₗᵢ[ℝ]  Submodule.map T Q := by exact?
  sorry

theorem linear_rupert_respects_subspace_iso (T : P ≃ₗᵢ[ℝ] P)
    (r : IsLinearRupertPairForSubspace X Y Q) : IsLinearRupertPairForSubspace X Y (Submodule.map T Q) := by
  let ⟨ Xi , Yi, clo_sub_int ⟩ := r
  let Xi' : P →ᵃⁱ[ℝ] P := T.toAffineIsometryEquiv.toAffineIsometry.comp Xi
  let Yi' : P →ᵃⁱ[ℝ] P := T.toAffineIsometryEquiv.toAffineIsometry.comp Yi
  use Xi', Yi'
  let Xs : Set Q := Q.orthogonalProjection ∘ Xi '' X
  let Ys : Set Q := Q.orthogonalProjection ∘ Yi '' Y
  let XsP_closure : closure (Q.subtype '' Xs) = Q.subtype '' (closure Xs) := by sorry
  let YsP_interior : interior (Q.subtype '' Ys) = Q.subtype '' (interior Ys) := by sorry
  change closure Xs ⊆ interior Ys at clo_sub_int
  have h : closure (Q.subtype '' Xs) ⊆ interior (Q.subtype '' Ys) := by
    rw [XsP_closure, YsP_interior]
    exact Set.image_mono clo_sub_int
  let Xs' := (Submodule.map T Q).orthogonalProjection ∘ Xi' '' X
  let Ys' := (Submodule.map T Q).orthogonalProjection ∘ Yi' '' Y
  change closure Xs' ⊆ interior Ys'

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
