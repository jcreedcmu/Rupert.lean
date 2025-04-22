import Mathlib
open Pointwise

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-
This is an alternative proof of subset_interior_hull as found in
Basic.lean at time of writing. Instead of relying on
mem_convexHull_iff_exists_fintype it relies on
segment_subset_convexHull.

To achieve parity with the other proof, it still needs a corollary
to replace the assumption
    h0 : Metric.ball 0 ε ⊆ X
with
    h0 : Metric.ball 0 ε ⊆ convexHull ℝ X
and
                  ℓ • X ⊆ ⋯
with
    convexHull ℝ (ℓ • X) ⊆ ⋯
in the conclusion. But these should be fairly easy.

Lemma:

If a convex set X of a euclidean space contains an open ball around
the origin, then for any ℓ ∈ (0,1), we have ℓ X ⊆ int(X).

Proof:

Let a point y ∈ ℓX be given. Hence there is x ∈ X with y = ℓx.
Suffices to show there's an open ball U ∋ y with U ⊆ X. Choose the
radius of U to be (1 - ℓ)ε. Let any point u ∈ U be given, we must show
u ∈ X. Since X is convex, it suffices to show u is on a line segment
between two points already in X. Choose the segment seg₁ --- seg₂,
where

   seg₁ := x
   seg₂ := (u - ℓx)/(1 - ℓ)

Observe that since ‖u - ℓx‖ < (1-ℓ)ε, we have ‖(u-ℓx)/(1-ℓ)‖ < ε,
hence seg₂ ∈ X by assumption that X contains the ε-ball about the
origin.

Then the claim that u is on the segment follows by computing

    ℓ seg₁ + (1 - ℓ) seg₂
  = ℓ x + u - ℓx
  = u
-/


lemma move_scale {n : ℕ} {s : ℝ} (sgz : s > 0) {v : E n} {Y : Set (E n)} :
     v ∈ s • Y → (1 / s) • v ∈ Y := by
  intro ⟨_, ⟨winy, factor⟩⟩
  rw [← factor, smul_smul]
  field_simp; exact winy

lemma subset_interior_hull' {n : ℕ} {X : Set (E n)} {ε ℓ: ℝ}
    (hε : 0 < ε)
    (hℓ : ℓ ∈ Set.Ioo 0 1)
    (h0 : Metric.ball 0 ε ⊆ X) :
    ℓ • X ⊆ interior (convexHull ℝ X) := by
  intro ix hix -- "inner x"
  apply Set.mem_sUnion.mpr

  have lnz : ℓ ≠ 0 := ne_of_gt (by (simp_all only [Set.mem_Ioo]))
  have olgz : 1 - ℓ > 0 := by simp_all only [Set.mem_Ioo, sub_pos]

  -- Here we choose the radius around ix that is fully contained in X.
  use Metric.ball ix ((1 - ℓ) * ε)

  have hb : 0 < (1 - ℓ) * ε := by simp_all only [Set.mem_Ioo, mul_pos_iff_of_pos_left, sub_pos]
  refine ⟨⟨Metric.isOpen_ball, ?_⟩, Metric.mem_ball_self hb⟩
  intro u hu

  let seg1 := (1/ℓ) • ix
  let seg2 := (1/(1-ℓ)) • (u - ix)

  have seg1_in_X : seg1 ∈ X := by -- "outer x" is still in X
      obtain ⟨w, winx, ix_eq_lw⟩ := hix
      simp only [seg1, ← ix_eq_lw]; rw [smul_smul]; field_simp
      exact winx

  have seg2_in_X : seg2 ∈ X := by
    refine h0 (move_scale olgz ?_)
    rw [smul_ball (ne_of_gt olgz) 0 ε, smul_zero,
        show (‖1-ℓ‖ = |1-ℓ|) from rfl,
        abs_of_pos olgz]
    simp_all only [Metric.mem_ball, dist_zero_right]
    exact hu

  have pt_in_seg : u ∈ segment ℝ seg1 seg2 := ⟨ ℓ, 1 - ℓ,
        ⟨ le_of_lt (by simp_all only [Set.mem_Ioo]),
          le_of_lt olgz,
          by simp_all only [add_sub_cancel],
          by rw [smul_smul, smul_smul]; field_simp ⟩⟩

  exact segment_subset_convexHull seg1_in_X seg2_in_X pt_in_seg
