import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_diagUnits2_mem_semiLocalIntegralSet_and_normString_eq_toTensorGL_of_ramificationIdx_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_diagUnits2_mem_semiLocalIntegralSet_and_normString_eq_toTensorGL_of_ramificationIdx_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1)
    (x y : (v.adicCompletionIntegers K)ˣ) :
    ∃ d₁ d₂ : (L ⊗[K] v.adicCompletion K)ˣ,
      diagUnits2 d₁ d₂ ∈ AutomorphicForm.semiLocalIntegralSet K L v ∧
      AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 d₁ d₂) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (diagUnits2 (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) :
              v.adicCompletionIntegers K →* v.adicCompletion K) x)
            (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) :
              v.adicCompletionIntegers K →* v.adicCompletion K) y)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_diagUnits2_mem_semiLocalIntegralSet_and_normString_eq_toTensorGL_of_ramificationIdx_eq_one.solution
