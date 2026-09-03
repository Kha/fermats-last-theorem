import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct Pointwise

theorem AutomorphicForm.setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : δ ∈ AutomorphicForm.semiLocalIntegralSet K L v)
    (hdisc : ∃ u ∈ AutomorphicForm.semiLocalIntegers K L v,
      u * (Matrix.trace ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ^ 2 -
            4 * Matrix.det ((AutomorphicForm.normString K L (v.adicCompletion K) σ δ :
              GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = 1) :
    {z : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
        z ∈ Subgroup.centralizer
            ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} :
              Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) ∧
          z⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ z ∈
            AutomorphicForm.semiLocalIntegralSet K L v} ⊆
      (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ :
          Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) * AutomorphicForm.semiLocalIntegralSet K L v := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one.solution
