import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isNormConjugator_one_of_idempotent_orbit

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.isNormConjugator_one_of_idempotent_orbit
    (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L)
    (e : L ⊗[K] A) (he : IsIdempotentElem e)
    (horth : ∀ i, 0 < i → i < Module.finrank K L → e * (⇑(sigmaTensor K L A σ))^[i] e = 0)
    (hsum : (∑ i ∈ Finset.range (Module.finrank K L), (⇑(sigmaTensor K L A σ))^[i] e) = 1)
    (γ : GL (Fin 2) A) :
    ∃ δ : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isNormConjugator_one_of_idempotent_orbit.solution
