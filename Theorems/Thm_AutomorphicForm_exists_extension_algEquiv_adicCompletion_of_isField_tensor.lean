import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_extension_algEquiv_adicCompletion_of_isField_tensor

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_extension_algEquiv_adicCompletion_of_isField_tensor
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hA : IsField (L ⊗[K] v.adicCompletion K)) :
    ∃ (w : v.Extension (𝓞 L))
      (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
      (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L),
      (∀ w' : v.Extension (𝓞 L), w' = w) ∧
      (∀ a : L ⊗[K] v.adicCompletion K, e (sigmaTensor K L (v.adicCompletion K) σ a) = θ (e a)) ∧
      (∀ x : L, e (x ⊗ₜ[K] 1) = algebraMap L (w.1.adicCompletion L) x) ∧
      orderOf θ = Module.finrank K L ∧
      (∀ y : w.1.adicCompletion L, θ y = y ↔
        y ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))) ∧
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L ∧
      Ideal.inertiaDeg' v.asIdeal w.1.asIdeal = Module.finrank K L := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_extension_algEquiv_adicCompletion_of_isField_tensor.solution
