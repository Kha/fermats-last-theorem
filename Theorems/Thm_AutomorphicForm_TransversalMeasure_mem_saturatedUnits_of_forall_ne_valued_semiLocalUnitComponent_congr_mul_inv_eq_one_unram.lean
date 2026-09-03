import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import P2M.Util
import P2M.Sol.S_AutomorphicForm_TransversalMeasure_mem_saturatedUnits_of_forall_ne_valued_semiLocalUnitComponent_congr_mul_inv_eq_one_unram

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.TransversalMeasure.mem_saturatedUnits_of_forall_ne_valued_semiLocalUnitComponent_congr_mul_inv_eq_one_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal = 1)
    (u : (L ⊗[K] v.adicCompletion K)ˣ) (w₀ : v.Extension (𝓞 L))
    (h : ∀ w : v.Extension (𝓞 L), w ≠ w₀ →
      Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w
        (Units.mapEquiv (Algebra.TensorProduct.congr σ
            (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv u * u⁻¹) :
          (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) = 1) :
    u ∈ AutomorphicForm.TransversalMeasure.saturatedUnits K L v := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_TransversalMeasure_mem_saturatedUnits_of_forall_ne_valued_semiLocalUnitComponent_congr_mul_inv_eq_one_unram.solution
