import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (hinert : Subsingleton (v.Extension (𝓞 L)))
    (c : L ⊗[K] v.adicCompletion K) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank K L),
        (⇑(AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ))^[i] c = (1 : L) ⊗ₜ[K] n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ) :
    (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.relIndex
        (((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
            ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ).toAddMonoidHom -
              AddMonoidHom.mulLeft c)) ⊓
          ((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring.toAddSubgroup.comap
            (AddMonoidHom.mulLeft ((1 : L) ⊗ₜ[K] (ϖ ^ s))))) =
      Ideal.absNorm v.asIdeal ^ min s m := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_relIndex_semiLocalIntegers_comap_sigmaTensor_sub_mulLeft_eq_absNorm_pow_min_of_subsingleton_extension.solution
