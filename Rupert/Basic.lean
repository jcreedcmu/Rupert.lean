import Mathlib

open scoped Matrix

notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- Projects a vector from `ℝ³` to `ℝ²` by ignoring the third coordinate. -/
def project32 (v : ℝ³) : ℝ² := ![v 0, v 1]

/-- The Rupert Property for a convex polyhedron given as a set of vertices. -/
def IsRupert (p : Set ℝ³) : Prop :=
   ∃ inner_rot ∈ SO3, ∃ outer_rot ∈ SO3, ∃ inner_offset : ℝ²,
   let inner_shadow := Set.image (λ t ↦ inner_offset + project32 (inner_rot *ᵥ t)) p
   let outer_shadow := Set.image (λ t ↦ project32 (outer_rot *ᵥ t)) p
   closure inner_shadow ⊆ interior (convexHull ℝ outer_shadow)

lemma closure_eq_of_finite {X : Type*} [TopologicalSpace X] [T1Space X]
    {s : Set X} (hs : s.Finite) : closure s = s :=
  closure_eq_iff_isClosed.mpr (hs.isClosed)

lemma subset_interior_hull {outer : Set ℝ²} {ε₀ ε₁: ℝ}
    (hε₀ : 0 < ε₀)
    (hε₁ : ε₁ ∈ Set.Ioo 0 1)
    (h0 : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer) :
    convexHull ℝ ((fun v : ℝ² ↦ (1 - ε₁) • v) '' outer) ⊆
      interior (convexHull ℝ outer) := by
  rw [Set.mem_Ioo] at hε₁
  obtain ⟨hε₁0, hε₁1⟩ := hε₁
  intro v h
  rw [mem_interior]
  use Metric.ball v (ε₀ * ε₁)
  refine ⟨?_, Metric.isOpen_ball, Metric.mem_ball_self (by positivity)⟩
  rw [mem_convexHull_iff_exists_fintype] at h
  obtain ⟨ι, x, w, g, hwp, hw1, hg, hwv⟩ := h
  intro v1 hv1
  have hb0 : (1 / ε₁) • (v1 - v) ∈ (convexHull ℝ) outer := by
    refine h0 ?_
    rw [Metric.mem_ball] at hv1 ⊢
    rw [dist_eq_norm] at hv1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs]
    have h1 : 0 < 1 / ε₁ := by positivity
    rw [abs_of_pos h1]
    suffices H : ‖v1 - v‖ < ε₀ * ε₁ by
      field_simp
      have : ‖v1 - v‖ / ε₁ < ε₀ * ε₁ / ε₁ :=
        (div_lt_div_iff_of_pos_right hε₁0).mpr H
      have h2 : ε₁ ≠ 0 := by positivity
      rwa [mul_div_cancel_right₀ _ h2] at this
    nlinarith only [hv1, hε₁0, hε₀]
  rw [mem_convexHull_iff_exists_fintype] at hb0 ⊢
  obtain ⟨ι₀, x₀, w₀, g₀, hwp₀, hw1₀, hg₀, hwv₀⟩ := hb0
  use ι ⊕ ι₀, inferInstance
  let w₁ : ι ⊕ ι₀ → ℝ := fun i ↦ match i with
    | .inl ii => (1 - ε₁) * w ii
    | .inr ii => ε₁ * w₀ ii
  let g₁ : ι ⊕ ι₀ → ℝ² := fun i ↦ match i with
    | .inl ii => (1 / (1 - ε₁)) • g ii
    | .inr ii => g₀ ii
  use w₁, g₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (i | i)
    · have h4 := hwp i
      simp [w₁]
      have h3 : 0 ≤ 1 - ε₁ := by linarith
      positivity
    · simp [w₁]
      specialize hwp₀ i
      positivity
  · simp [Fintype.sum_sum_type, w₁, ←Finset.mul_sum, hw1₀, hw1]
  · rintro (i | i)
    · dsimp only [g₁]
      specialize hg i
      simp at hg
      obtain ⟨y, hy, hy1⟩ := hg
      symm at hy1
      apply_fun ((1/(1-ε₁)) • ·) at hy1
      rw [←smul_assoc] at hy1
      have h3 : 0 < 1 - ε₁ := by linarith
      field_simp at hy1
      rw [←hy1] at hy
      exact hy
    · dsimp only [g₁]
      exact hg₀ i
  · simp only [Fintype.sum_sum_type, w₁, g₁]
    have h1 : ∀ x : ι₀, (ε₁ * w₀ x) • g₀ x = ε₁ • (w₀ x • g₀ x) := by
      intro x
      exact mul_smul ε₁ (w₀ x) (g₀ x)
    rw [Fintype.sum_congr _ _ h1, ←Finset.smul_sum, hwv₀]
    have h2 : ∀ x : ι, ((1 - ε₁) * w x) • (1 / (1 - ε₁)) • g x = w x • g x := by
      intro x
      rw [smul_comm, mul_smul]
      rw [←smul_assoc]
      have h3 : 0 < 1 - ε₁ := by linarith
      field_simp
    rw [Fintype.sum_congr _ _ h2, hwv]
    rw [←smul_assoc]
    field_simp

lemma mem_interior_hull {outer : Set ℝ²} {ε₀ ε₁ : ℝ}
    (hε₀ : 0 < ε₀)
    (hε₁ : ε₁ ∈ Set.Ioo 0 1)
    (h0 : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer)
    {p : ℝ²}
    (h : p ∈ convexHull ℝ ((fun v : ℝ² ↦ (1 - ε₁) • v) '' outer)) :
    p ∈ interior (convexHull ℝ outer) := by
  revert h p
  convert subset_interior_hull hε₀ hε₁ h0
