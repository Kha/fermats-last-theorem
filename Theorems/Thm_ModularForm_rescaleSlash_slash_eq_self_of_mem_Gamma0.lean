import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_rescaleSlash_slash_eq_self_of_mem_Gamma0
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat

open scoped ModularForm
theorem ModularForm.rescaleSlash_slash_eq_self_of_mem_Gamma0 {R M d : ℕ} [NeZero M]
    (hdRM : d * R ∣ M) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 R : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (SlashAction.map k (ModularForm.heckeDiagMatrix d) f)
      = SlashAction.map k (ModularForm.heckeDiagMatrix d) f := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_rescaleSlash_slash_eq_self_of_mem_Gamma0.solution
