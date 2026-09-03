import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_exists_heckeAlgebraChar_raisedLevel
attribute [-simp] FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false
theorem CuspForm.IsNormalizedEigenform.exists_heckeAlgebraChar_raisedLevel
    {N q' : ℕ} [NeZero N] (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) [NeZero (N * q')]
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : CuspForm.IsNormalizedEigenform f) :
    ∃ χ₁ : CuspForm.heckeAlgebra (N * q') 2 {ℓ | ℓ ∣ N * q'} →+* integralClosure ℤ ℂ,
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q'),
        ((χ₁ (CuspForm.heckeAlgebra.T hℓ hℓM hℓM) : integralClosure ℤ ℂ) : ℂ)
          = ModularFormClass.qCoeff f ℓ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_exists_heckeAlgebraChar_raisedLevel.solution
