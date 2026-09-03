import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve ModularCurve.IgusaScheme

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    ∃ w : ↥(chartAlgFin (N * p) p) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p),
      (∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
        atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p)))) ∧
      w.trans w = AlgEquiv.refl := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull.solution
