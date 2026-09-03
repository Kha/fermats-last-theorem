import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (c : w.1.adicCompletion L) (hc : ‖c‖ ≠ 1) (y : w.1.adicCompletion L) :
    ‖θ y - c * y‖ = ‖y‖ * max 1 ‖c‖ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one.solution
