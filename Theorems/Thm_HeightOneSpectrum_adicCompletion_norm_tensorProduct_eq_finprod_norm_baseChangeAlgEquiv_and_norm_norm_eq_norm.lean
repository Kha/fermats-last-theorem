import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (∀ x : L ⊗[K] v.adicCompletion K,
      Algebra.norm (v.adicCompletion K) x =
        ∏ᶠ w : v.Extension (𝓞 L),
          Algebra.norm (v.adicCompletion K)
            (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w)) ∧
    (∀ (w : v.Extension (𝓞 L)) (y : w.1.adicCompletion L),
      ‖Algebra.norm (v.adicCompletion K) y‖ = ‖y‖) ∧
    (∀ x : L ⊗[K] v.adicCompletion K,
      ‖Algebra.norm (v.adicCompletion K) x‖ =
        ∏ᶠ w : v.Extension (𝓞 L), ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w‖) := by p2m_exact_reverting @_root_.P2MW.S_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm.solution
