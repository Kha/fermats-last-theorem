import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem AlgebraicGeometry.Scheme.IdealSheafData.eq_iff_comap_subschemeInclusion_eq_bot
    {W : Scheme.{u}} (I₁ I₂ : W.IdealSheafData) :
    I₁ = I₂ ↔ I₂.comap I₁.subschemeι = ⊥ ∧ I₁.comap I₂.subschemeι = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot.solution
