import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_NumberField_nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hsplit : Nontrivial (v.Extension (𝓞 L))) :
    Nonempty (L →ₐ[K] v.adicCompletion K) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime.solution
