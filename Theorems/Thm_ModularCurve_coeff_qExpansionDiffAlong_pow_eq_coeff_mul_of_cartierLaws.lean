import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (F : IntermediateField K (LaurentSeries K)) [AlgebraicCurve.IsCurveOver K ↥F]
    (x : ↥F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set ↥F)) ↥F]
    (C : Ω[↥F⁄K] →+ Ω[↥F⁄K])
    (hC1 : ∀ (f : ↥F) (ω : Ω[↥F⁄K]), C (f ^ p • ω) = f • C ω)
    (hC2 : ∀ f : ↥F, C (KaehlerDifferential.D K ↥F f) = 0)
    (hC3 : ∀ f : ↥F, C (f ^ (p - 1) • KaehlerDifferential.D K ↥F f) = KaehlerDifferential.D K ↥F f)
    (ω : Ω[↥F⁄K]) (n : ℤ) :
    (ModularCurve.qExpansionDiffAlong F.val (C ω)).coeff n ^ p =
      (ModularCurve.qExpansionDiffAlong F.val ω).coeff (n * p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws.solution
