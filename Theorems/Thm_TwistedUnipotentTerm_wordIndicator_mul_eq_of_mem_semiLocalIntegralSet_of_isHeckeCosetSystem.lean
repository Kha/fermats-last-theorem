import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem TwistedUnipotentTerm.wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (g : GL (Fin 2) (w.1.adicCompletion L))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) g rT)
    (z : GL (Fin 2) (w.1.adicCompletion L)) (hz : ∀ y : GL (Fin 2) (w.1.adicCompletion L), z * y = y * z)
    (k j : ℕ) (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hs : s ∈ AutomorphicForm.semiLocalIntegralSet K L v)
    (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    TwistedUnipotentTerm.wordIndicator K L v w n rT z k j (s * x) =
        TwistedUnipotentTerm.wordIndicator K L v w n rT z k j x ∧
      TwistedUnipotentTerm.wordIndicator K L v w n rT z k j (x * s) =
        TwistedUnipotentTerm.wordIndicator K L v w n rT z k j x := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem.solution
