import Definitions.Def_ModularCurve_DRModelPackageLevel
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve.IgusaScheme ModularCurve.DRLevel open ModularCurve hiding atkinLehnerInvolutionFull_apply_apply

namespace ModularCurve.DRModelPackageLevel

theorem iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (a b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hab : Ideal.span {a} ⊔ Ideal.span {𝔓.theta b} = ⊤)
    (𝔮 𝔮' : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (ha : a ∈ 𝔮.asIdeal) (hb : b ∈ 𝔮'.asIdeal) :
    (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 ≠ 𝔓.w.hom.base ((IgusaScheme.ιFin (N₀ * q) q).base 𝔮') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top.solution

end ModularCurve.DRModelPackageLevel
