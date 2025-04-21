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
       ext i j
       fin_cases i, j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, inner_rot]
     · -- to show: inner_rot * star inner_rot = 1
       ext i j
       fin_cases i, j <;> simp [inner_rot, Matrix.vecMul]

   constructor
   · exact unitary
   · simp [inner_rot, det_succ_row_zero, Fin.sum_univ_succ]

 have outer_rot_so3 : outer_rot ∈ SO3 := by
   have unitary : outer_rot ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
    constructor
    · ext i j
      fin_cases i, j <;>
        simp [outer_rot, Matrix.mul_apply, Fin.sum_univ_succ, rh_lemma]
    · ext i j
      fin_cases i, j <;>
        simp [outer_rot, Matrix.vecMul, rh_lemma]

   constructor
   · exact unitary
   · simp [outer_rot, det_succ_row_zero, Fin.sum_univ_succ, rh_lemma]

 use inner_rot, inner_rot_so3, outer_rot, outer_rot_so3, inner_offset

 intro inner_shadow outer_shadow x hx
 have hisf : inner_shadow.Finite := by
   have hsf : square.Finite := by unfold square; exact Set.toFinite _
   exact Set.Finite.image _ hsf
 rw [closure_eq_of_finite hisf] at hx
 obtain ⟨y, ⟨y_in_square, proj_rot_y_eq_x ⟩⟩ := hx

 obtain ⟨ε₀, hε₀0, hε₀⟩ : ∃ ε₀, 0 < ε₀ ∧ ε₀ < √2/4 := by
   sorry
 have zero_in_outer : Metric.ball 0 ε₀ ⊆ convexHull ℝ outer_shadow := by
   intro v hv
   simp only [Metric.mem_ball, dist_zero_right, outer_rot, inner_rot] at hv
   rw [mem_convexHull_iff_exists_fintype]
   use Fin 4, inferInstance
   use ![1/4 + v 0 / √2, 1/4 - v 0 / √2, 1/4 + v 1 / √2, 1/4 - v 1 / √2]
   use ![![√2, 0],![-√2, 0], ![0, √2],![0, -√2]]
   have h0 : v 0 < ε₀ := by sorry
   have h2 : -ε₀ < v 0 := sorry
   have h3 : v 1 < ε₀ := by sorry
   have h4 : -ε₀ < v 1 := sorry
   refine ⟨?_, ?_, ?_, ?_⟩
   · intro i
     fin_cases i
     · simp
       suffices H : 0 ≤ 4⁻¹ + ε₀ / √2 by sorry
       sorry
     · simp
       sorry
     · simp
       sorry
     · simp
       sorry
   · sorry
   · sorry
   · sorry

 -- subset_interior_hull
 let ε₁ : ℝ := 0.001
 have hε₁ : ε₁ ∈ Set.Ioo 0 1 := by norm_num

 have negx_in_outer : ![-1, 0] ∈ interior (convexHull ℝ outer_shadow) := by
   apply mem_interior_hull hε₀0 hε₁ zero_in_outer
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
 rcases y_in_square with rfl | rfl | rfl | rfl
 all_goals (unfold Matrix.mulVec; simp[inner_rot, project32])
 · exact negx_in_outer
 · exact posx_in_outer
 · exact negx_in_outer
 · exact posx_in_outer

end square_is_rupert
