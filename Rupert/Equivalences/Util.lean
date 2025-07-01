import Mathlib
import Rupert.Basic
import Rupert.Set
open Pointwise
open Matrix

/-- Projecting from ℝ³ to ℝ² is linear -/
noncomputable
def proj_xy_linear : ℝ³ →ₗ[ℝ] ℝ² :=
  {
   toFun := proj_xy,
   map_add' := by
     intro x y;
     ext i; fin_cases i;
     · simp only [proj_xy, Fin.isValue, PiLp.add_apply, Fin.zero_eta, cons_val_zero];
     · simp only [proj_xy, Fin.isValue, PiLp.add_apply, Fin.mk_one, cons_val_one, cons_val_fin_one]
   ,
   map_smul' := by
     intro x y; ext i; fin_cases i;
     · simp only [proj_xy, Fin.isValue, PiLp.smul_apply, smul_eq_mul, Fin.zero_eta, cons_val_zero,
       RingHom.id_apply];
     · simp only [proj_xy, Fin.isValue, PiLp.smul_apply, smul_eq_mul, Fin.mk_one, cons_val_one,
       cons_val_fin_one, RingHom.id_apply]
   }

noncomputable
def rotation_affine (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ³ := (Matrix.mulVecLin rot).toAffineMap

/-- Translating is affine. -/
noncomputable
def offset_affine (off : E 2) : ℝ² →ᵃ[ℝ] ℝ² :=
  {toFun v := off + v, linear := LinearMap.id, map_vadd' p v := add_vadd_comm v off p }

noncomputable
def proj_xy_rotation_is_affine (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ² :=
  AffineMap.comp proj_xy_linear.toAffineMap (rotation_affine rot)

noncomputable
def full_transform_affine (off : E 2) (rot : SO3) : ℝ³ →ᵃ[ℝ] ℝ² :=
  AffineMap.comp (offset_affine off) (proj_xy_rotation_is_affine rot)
