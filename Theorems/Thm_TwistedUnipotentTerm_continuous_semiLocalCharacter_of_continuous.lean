import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_continuous_semiLocalCharacter_of_continuous

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem TwistedUnipotentTerm.continuous_semiLocalCharacter_of_continuous
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (TwistedUnipotentTerm.semiLocalCharacter K L ξL v) := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_continuous_semiLocalCharacter_of_continuous.solution
