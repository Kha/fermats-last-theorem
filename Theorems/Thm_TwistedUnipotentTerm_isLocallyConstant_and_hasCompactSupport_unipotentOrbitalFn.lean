import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem TwistedUnipotentTerm.isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
    (k j : ℕ) :
    IsLocallyConstant (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j) ∧
      HasCompactSupport (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w n rT z k j) := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_isLocallyConstant_and_hasCompactSupport_unipotentOrbitalFn.solution
