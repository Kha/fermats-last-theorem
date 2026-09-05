import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
import P2M.Util
namespace P2MW.S_AutomorphicForm_norm_algebraNorm_eq_prod_norm_baseChangeAlgEquiv_apply

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))]
    (α : L ⊗[K] v.adicCompletion K) :
    ‖Algebra.norm (v.adicCompletion K) α‖ =
      ∏ w : v.Extension (𝓞 L), ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v α w‖ := by
  rw [← finprod_eq_prod_of_fintype]
  exact (HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
    K L v).2.2 α

