import Mathlib
import Rupert.Basic
import Rupert.LinearRupert

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P] (X Y : Set P)

theorem coatomic_subspaces_equivalent (Q1 Q2 : Submodule ℝ P) (_ : IsCoatom Q1) (_ : IsCoatom Q2) :
    ∃ T : P →ₗᵢ[ℝ] P, Submodule.map T Q1 = Q2 := by
  sorry

theorem linear_rupert_respects_subspace_iso (Q : Submodule ℝ P) [Nonempty Q]
    (T : P →ₗᵢ[ℝ] P) :
    IsLinearRupertPairForSubspace X Y Q → IsLinearRupertPairForSubspace X Y (Submodule.map T Q) := by
  sorry

theorem rupert_for_one_subspace_imp_for_all {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    (X Y : Set P) (Q : Submodule ℝ P) [Nonempty Q] (Qcoatom : IsCoatom Q) :
    IsLinearRupertPair X Y → IsLinearRupertPairForSubspace X Y Q := by
  intro ⟨ Q', Q'inh, Q'coatom, hrup ⟩
  let ⟨ T, hT ⟩ := coatomic_subspaces_equivalent Q' Q Q'coatom Qcoatom
  simp only [← hT]
  exact linear_rupert_respects_subspace_iso X Y Q' T hrup
