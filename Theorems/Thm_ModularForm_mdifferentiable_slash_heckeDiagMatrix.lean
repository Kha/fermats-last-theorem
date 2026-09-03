import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularForm_mdifferentiable_slash_heckeDiagMatrix
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat

open scoped ModularForm
theorem ModularForm.mdifferentiable_slash_heckeDiagMatrix (d : ℕ) (k : ℤ)
    {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (SlashAction.map k (ModularForm.heckeDiagMatrix d) f) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_mdifferentiable_slash_heckeDiagMatrix.solution
