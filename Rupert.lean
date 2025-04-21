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

-- ∃ ε, ∀ p ∈ inner_shadow, ε-ball centered a p ⊆ outshadow

lemma closure_eq_of_finite {X : Type*} [TopologicalSpace X] [T1Space X]
    {s : Set X} (hs : s.Finite) : closure s = s :=
  closure_eq_iff_isClosed.mpr (hs.isClosed)

lemma foo (inner outer : Set ℝ²) (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1)
    (h0 : 0 ∈ convexHull ℝ outer)
    (h : inner ⊆ convexHull ℝ ((fun v : ℝ² ↦ (1 - ε) • v) '' outer)) :
    inner ⊆ interior (convexHull ℝ outer) := by
  rw [Set.mem_Ioo] at hε
  intro v hv
  rw [Set.subset_def] at h
  specialize h v hv
  rw [mem_interior]
  use Metric.ball v ε
  refine ⟨?_, Metric.isOpen_ball, Metric.mem_ball_self hε.1⟩
  rw [mem_convexHull_iff_exists_fintype] at h
  obtain ⟨ι, x, w, g, hwp, hw1, hg, hwv⟩ := h
  intro v1 hv1
  sorry
