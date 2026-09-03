import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_setIntegral_integral_semiLocalCharacter_mul_wordIndicator_eq_integral_mul_setIntegral

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] AutomorphicForm.glBorelOf

open scoped TensorProduct.RightActions in
theorem TwistedUnipotentTerm.setIntegral_integral_semiLocalCharacter_mul_wordIndicator_eq_integral_mul_setIntegral
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
    (μZ : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μZ.IsHaarMeasure]
    (hξvc : Continuous (TwistedUnipotentTerm.semiLocalCharacter K L ξL v))
    (k j : ℕ) (y : L ⊗[K] v.adicCompletion K) :
    ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v, ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
        TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
          TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v y) ∂μZ
      ∂(AutomorphicForm.semiLocalHaar K L v) =
    ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
      TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
        ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v y)
          ∂(AutomorphicForm.semiLocalHaar K L v) ∂μZ := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_setIntegral_integral_semiLocalCharacter_mul_wordIndicator_eq_integral_mul_setIntegral.solution
