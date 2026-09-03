import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ σ : modularFunctionFieldFullC K N ≃ₐ[K] modularFunctionFieldFullC K N,
      σ ⟨jqModC K, jqModC_mem_full K N⟩ = ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ ∧
      σ ⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ = ⟨jqModC K, jqModC_mem_full K N⟩ ∧
      ∀ x, σ (σ x) = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC.solution
