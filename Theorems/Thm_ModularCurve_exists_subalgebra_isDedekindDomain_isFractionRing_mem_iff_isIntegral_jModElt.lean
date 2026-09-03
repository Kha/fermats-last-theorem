import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

universe u

theorem ModularCurve.exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt
    (K : Type u) [Field K] [DecidableEq K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ A : Subalgebra K ↥(ModularCurve.modularFunctionFieldFullC K N),
      IsDedekindDomain ↥A ∧ IsFractionRing ↥A ↥(ModularCurve.modularFunctionFieldFullC K N) ∧
        ∀ a : ↥(ModularCurve.modularFunctionFieldFullC K N), a ∈ A ↔ (∃ P : Polynomial (Polynomial K), P.Monic ∧ Polynomial.eval₂ (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))).toRingHom a P = 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt.solution
