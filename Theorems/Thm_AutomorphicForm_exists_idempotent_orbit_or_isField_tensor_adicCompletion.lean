import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_idempotent_orbit_or_isField_tensor_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.exists_idempotent_orbit_or_isField_tensor_adicCompletion
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    (∃ e : L ⊗[K] v.adicCompletion K, IsIdempotentElem e ∧
        (∀ i, 0 < i → i < Module.finrank K L →
          e * (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i] e = 0) ∧
        (∑ i ∈ Finset.range (Module.finrank K L),
          (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[i] e) = 1) ∨
      IsField (L ⊗[K] v.adicCompletion K) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_idempotent_orbit_or_isField_tensor_adicCompletion.solution
