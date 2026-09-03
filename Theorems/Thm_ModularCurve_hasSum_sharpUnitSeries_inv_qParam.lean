import Definitions.Def_ModularCurve_EtaQuotient
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_sharpUnitSeries_inv_qParam
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

theorem ModularCurve.hasSum_sharpUnitSeries_inv_qParam (ℓ : ℕ) [NeZero ℓ] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((ModularCurve.sharpUnitSeries ℓ)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) ((ModularCurve.sharpUnitFun ℓ τ)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_sharpUnitSeries_inv_qParam.solution
