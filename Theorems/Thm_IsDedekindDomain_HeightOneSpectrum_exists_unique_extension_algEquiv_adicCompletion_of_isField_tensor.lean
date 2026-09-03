import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem IsDedekindDomain.HeightOneSpectrum.exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor
    (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    (v : HeightOneSpectrum (𝓞 F)) (hA : IsField (M ⊗[F] v.adicCompletion F)) :
    ∃ (w : v.Extension (𝓞 M))
      (e : (M ⊗[F] v.adicCompletion F) ≃ₐ[v.adicCompletion F] w.1.adicCompletion M),
      (∀ w' : v.Extension (𝓞 M), w' = w) ∧
      (∀ x : M, e (x ⊗ₜ[F] 1) = algebraMap M (w.1.adicCompletion M) x) ∧
      Module.finrank (v.adicCompletion F) (w.1.adicCompletion M) = Module.finrank F M := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_unique_extension_algEquiv_adicCompletion_of_isField_tensor.solution
