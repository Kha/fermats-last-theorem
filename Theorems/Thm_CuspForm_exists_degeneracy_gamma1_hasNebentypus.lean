import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_exists_degeneracy_gamma1_hasNebentypus
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_degeneracy_gamma1_hasNebentypus
    {k : ℤ} {M N d : ℕ} [NeZero N] (hd : M * d ∣ N) (g : CuspForm (Gamma1 M) k) :
    ∃ G : CuspForm (Gamma1 N) k,
      (∀ τ : UpperHalfPlane, G τ = g (ModularForm.heckeDiagMatrix d • τ)) ∧
      (∀ n : ℕ, ModularFormClass.qCoeff G n =
        if d ∣ n then ModularFormClass.qCoeff g (n / d) else 0) ∧
      ∀ ε : DirichletCharacter ℂ M, CuspForm.HasNebentypus ε g →
        CuspForm.HasNebentypus (DirichletCharacter.changeLevel (dvd_of_mul_right_dvd hd) ε) G := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_degeneracy_gamma1_hasNebentypus.solution
