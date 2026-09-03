import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime]
    (hdeg : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K ℓ} : Set (LaurentSeries K))) = dedekindPsi ℓ) :
    ∃ σ : modularFunctionFieldC K ℓ ≃ₐ[K] modularFunctionFieldC K ℓ,
      σ ⟨jqModC K, jqModC_mem K ℓ⟩ = ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩ ∧
      σ ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩ = ⟨jqModC K, jqModC_mem K ℓ⟩ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi.solution
