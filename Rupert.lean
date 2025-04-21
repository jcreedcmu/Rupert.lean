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
  use Metric.ball v (ε₀ * ε₁ / 2)
  refine ⟨?_, Metric.isOpen_ball, Metric.mem_ball_self (by positivity)⟩
  rw [mem_convexHull_iff_exists_fintype] at h
  obtain ⟨ι, x, w, g, hwp, hw1, hg, hwv⟩ := h
  intro v1 hv1
  rw [mem_convexHull_iff_exists_fintype]
  use ι ⊕ Unit, inferInstance
  let w₁ : ι ⊕ Unit → ℝ := fun i ↦ match i with
    | .inl ii => (1 - ε₁) * w ii
    | .inr () => ε₁
  let g₁ : ι ⊕ Unit → ℝ² := fun i ↦ match i with
    | .inl ii => (1 / (1 - ε₁)) • g ii
    | .inr () => v1 - v
  use w₁, g₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (i | i)
    · have := hwp i
      simp [w₁]
      sorry
    · sorry
  · sorry
  · sorry
  · sorry


lemma mem_interior_hull {outer : Set ℝ²} {ε₀ ε₁ : ℝ}
    (hε₀ : 0 < ε₀)
    (hε₁ : ε₁ ∈ Set.Ioo 0 1)
    (h0 : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer)
    {p : ℝ²}
    (h : p ∈ convexHull ℝ ((fun v : ℝ² ↦ (1 - ε₁) • v) '' outer)) :
    p ∈ interior (convexHull ℝ outer) := by
  revert h p
  convert subset_interior_hull hε₀ hε₁ h0

section square_is_rupert
/- In this section we aim to show that the square has the rupert property.
   Status:
   - Still need to show that the shadow of any point from the inner square is in the
     interior of the shadow of the outer square.
-/
open Matrix
open Real
def square : Set ℝ³ := { ![-1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, 0] }

noncomputable
def rh : ℝ := √2/2 -- square root of one-half

-- A simple algebraic fact about √2/2 that arises multiple times
-- FIXME: is there a systematic naming convention that would give me a less
-- opaque name for this
theorem rh_lemma : rh * rh + rh * rh  = 1 := by
  calc rh * rh + rh * rh
       _ = 2 * (√2 / 2)^2 := by rw[rh]; ring
       _ = 2 * ((√2 * √2) / 2^2) := by rw[div_pow]; ring
       _ = 2 * (2 / 2^2) := by rw[mul_self_sqrt (by norm_num)]
       _ = 1 := by norm_num

set_option maxHeartbeats 10000000 in
theorem square_is_rupert : IsRupert square := by
/-

The diagram shows the (x,y) plane, the z axis runs through the
screen. The rotation inner_rot rotates about the x axis, creating the
horizontal slot shape.  The rotation outer_rot rotates the (x,y) plane
by π/4 radians. No offset translation is needed.

      +
     / \
    /   \
   /     \
  + ----- +
   \     /
    \   /
     \ /
      +
-/
 let inner_rot : Matrix (Fin 3) (Fin 3) ℝ :=
   !![1, 0, 0;
      0, 0,-1;
      0, 1, 0]
 let outer_rot : Matrix (Fin 3) (Fin 3) ℝ :=
   !![ rh, rh, 0;
      -rh, rh, 0;
        0,  0, 1]
 let inner_offset : ℝ² := 0

 have inner_rot_so3 : inner_rot ∈ SO3 := by
   have unitary : inner_rot ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
     change star inner_rot * inner_rot = 1 ∧ inner_rot * star inner_rot = 1
     constructor
     · -- to show: star inner_rot * inner_rot = 1
       simp [inner_rot]
       ext i j; simp [Matrix.mul_apply, Fin.sum_univ_succ]
       fin_cases i, j <;> simp
     · -- to show: inner_rot * star inner_rot = 1
       ext i j;
       simp [inner_rot]
       unfold Matrix.vecMul
       fin_cases i, j <;> simp

   constructor
   · exact unitary
   · simp [inner_rot, det_succ_row_zero, Fin.sum_univ_succ]

 have outer_rot_so3 : outer_rot ∈ SO3 := by
   have unitary : outer_rot ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
    constructor
    · ext i j
      simp [outer_rot, Matrix.mul_apply, Fin.sum_univ_succ]
      fin_cases i, j <;> simp
      all_goals (exact rh_lemma)
    · ext i j
      simp [outer_rot]; unfold Matrix.vecMul
      fin_cases i, j
      all_goals simp
      all_goals (exact rh_lemma)

   constructor
   · exact unitary
   · simp [outer_rot, det_succ_row_zero, Fin.sum_univ_succ]
     exact rh_lemma

 use inner_rot, inner_rot_so3, outer_rot, outer_rot_so3, inner_offset

 intro inner_shadow outer_shadow x hx
 have hisf : inner_shadow.Finite := by
   have hsf : square.Finite := by unfold square; exact Set.toFinite _
   exact Set.Finite.image _ hsf
 rw [closure_eq_of_finite hisf] at hx
 obtain ⟨y, ⟨y_in_square, proj_rot_y_eq_x ⟩⟩ := hx

 let ε₀ : ℝ := 0.01
 have zero_in_outer : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer_shadow := by
   intro v hv
   simp only [Metric.mem_ball, dist_zero_right, outer_rot, inner_rot] at hv
   rw [mem_convexHull_iff_exists_fintype]

   sorry
   /-
   use Fin 2, inferInstance, ![1/2, 1/2], ![![-rh * 2, 0], ![rh * 2 , 0]]
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro i; fin_cases i <;> simp
   · norm_num
   · intro i
     unfold outer_shadow square project32 outer_rot rh
     fin_cases i
     · use ![-1, -1, 0]
       simp
       ext i; fin_cases i <;> simp
       ring
     · use ![1, 1, 0]; simp
   · ext i
     fin_cases i <;> simp
-/

 -- subset_interior_hull
 let ε₁ : ℝ := 0.001
 have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num

 have negx_in_outer : ![-1, 0] ∈ interior (convexHull ℝ outer_shadow) := by
   apply mem_interior_hull (by norm_num) hε₁ zero_in_outer
   rw [mem_convexHull_iff_exists_fintype]
   -- we need to write (-1,0) as a convex combination of
   -- (-(1-ε)√2, 0), ((1-ε)√2, 0)
   use Fin 2, inferInstance
   use ![((1-ε₁)* √2 - 1) / (2 * (1 - ε₁) * √2),
         ((1-ε₁)* √2 + 1) /(2 * (1 - ε₁) * √2)]
   use ![![(1-ε₁) * √2, 0], ![-(1-ε₁) * √2, 0]]
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro i; fin_cases i
     · simp [ε₁]
       have h1 : 0 ≤ 2 * (1 - 1e-3) * √2 := by positivity
       suffices H : (0:ℝ) ≤ ((1 - 1e-3) * √2 - 1) from div_nonneg H h1
       suffices H : (1:ℝ) ≤ (1 - 1e-3) * √2 by linarith
       refine (sq_le_sq₀ zero_le_one (by positivity)).mp ?_
       rw [mul_pow, Real.sq_sqrt zero_le_two]
       norm_num
     · simp [ε₁]
       have h1 : 0 ≤ 2 * (1 - 1e-3) * √2 := by positivity
       suffices H : (0:ℝ) ≤ ((1 - 1e-3) * √2 + 1) from div_nonneg H h1
       suffices H : (1:ℝ) ≤ (1 - 1e-3) * √2 by linarith
       refine (sq_le_sq₀ zero_le_one (by positivity)).mp ?_
       rw [mul_pow, Real.sq_sqrt zero_le_two]
       norm_num
   · field_simp; ring
   · intro i
     fin_cases i
     · unfold outer_shadow square project32 outer_rot rh
       simp
       use ![√2, 0]
       constructor
       · right; right; right; rfl
       · ext i
         fin_cases i <;> simp
     · dsimp
       simp [outer_shadow, square, project32, outer_rot, rh, Matrix.mulVec]
       use ![-√2, 0]
       constructor
       · left
         ext i; fin_cases i
         · simp; ring
         · simp
       · ext i; fin_cases i
         · simp; ring
         · simp
   · ext i
     fin_cases i
     · simp
       field_simp; ring
     · field_simp
 have posx_in_outer : ![1, 0] ∈ interior (convexHull ℝ outer_shadow) := sorry

 -- we have y ∈ ℝ³ that came from the square, which after being rotated by
 -- inner_rot and projected, is x
 rw [← proj_rot_y_eq_x]; unfold inner_offset; simp;
 rcases y_in_square with h | h | h | h
 all_goals (rw [h]; unfold Matrix.mulVec; simp[inner_rot, project32])
 · exact negx_in_outer
 · exact posx_in_outer
 · exact negx_in_outer
 · exact posx_in_outer

end square_is_rupert
