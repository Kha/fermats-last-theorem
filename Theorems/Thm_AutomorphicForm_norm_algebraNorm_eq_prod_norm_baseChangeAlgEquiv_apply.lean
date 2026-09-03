import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))]
    (α : L ⊗[K] v.adicCompletion K) :
    ‖Algebra.norm (v.adicCompletion K) α‖ =
      ∏ w : v.Extension (𝓞 L), ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v α w‖ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply.solution
