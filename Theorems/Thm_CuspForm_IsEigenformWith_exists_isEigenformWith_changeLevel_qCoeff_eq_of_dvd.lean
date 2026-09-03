import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_IsEigenformWith_exists_isEigenformWith_changeLevel_qCoeff_eq_of_dvd
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.IsEigenformWith.exists_isEigenformWith_changeLevel_qCoeff_eq_of_dvd
    {M : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (hg : CuspForm.IsEigenformWith ε g) {N : ℕ} [NeZero N] (hMN : M ∣ N) :
    ∃ h : CuspForm (Gamma1 N) k,
      CuspForm.IsEigenformWith (DirichletCharacter.changeLevel hMN ε) h ∧
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ ∣ N → ℓ ∣ M) →
        ModularFormClass.qCoeff h ℓ = ModularFormClass.qCoeff g ℓ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsEigenformWith_exists_isEigenformWith_changeLevel_qCoeff_eq_of_dvd.solution
