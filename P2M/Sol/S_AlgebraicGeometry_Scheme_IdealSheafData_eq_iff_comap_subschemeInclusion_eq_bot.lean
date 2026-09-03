import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem solution
    {W : Scheme.{u}} (I₁ I₂ : W.IdealSheafData) :
    I₁ = I₂ ↔ I₂.comap I₁.subschemeι = ⊥ ∧ I₁.comap I₂.subschemeι = ⊥ := by
  have key : ∀ (I J : W.IdealSheafData), J.comap I.subschemeι = ⊥ ↔ J ≤ I := by
    intro I J
    rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot,
      Scheme.IdealSheafData.ker_subschemeι]
  rw [key, key, le_antisymm_iff, and_comm]
