import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem TwistedUnipotentTerm.isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (m : ℕ) (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ) :
    IsLocallyConstant (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j) ∧
      HasCompactSupport (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j) := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport.solution
