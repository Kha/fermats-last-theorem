import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
namespace P2MW.S_PeriodPair_weierstrassP_scale

set_option autoImplicit false

noncomputable section

open PeriodPair

theorem solution (L : PeriodPair) (α : ℂˣ) (z : ℂ) :
    (L.scale α).weierstrassP ((α : ℂ) * z) = ((α : ℂ) ^ 2)⁻¹ * L.weierstrassP z := by
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP,
    ← (L.scale α).latticeEquivProd.symm.toEquiv.tsum_eq,
    ← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
  congr 1 with p
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, scale_ω₁, scale_ω₂]
  rw [show (α : ℂ) * z - ((p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂)) =
      α * (z - (p.1 * L.ω₁ + p.2 * L.ω₂)) by ring,
    show ((p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂)) = α * (p.1 * L.ω₁ + p.2 * L.ω₂) by ring,
    mul_pow, mul_pow, one_div, one_div, one_div, one_div, mul_inv, mul_inv, mul_sub]
