import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import P2M.Util
import P2M.Sol.S_TwistedUnipotentTerm_wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem TwistedUnipotentTerm.wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
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
    (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (Ideal.absNorm w.1.asIdeal + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + Ideal.absNorm w.1.asIdeal * W k (d + 2))
    (k j : ℕ) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) (x : L ⊗[K] v.adicCompletion K) :
    (TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
          (TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x) ≠ 0 →
        (∀ w' : v.Extension (𝓞 L), w' ≠ w →
            Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w' ζ : (w'.1.adicCompletion L)ˣ) :
                w'.1.adicCompletion L) = 1 ∧
              HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈
                w'.1.adicCompletionIntegers L) ∧
          Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) :
              w.1.adicCompletion L) ^ 2 =
            Valued.v (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ) ^ (k + 2 * j)) ∧
      ((∀ w' : v.Extension (𝓞 L), w' ≠ w →
          Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w' ζ : (w'.1.adicCompletion L)ˣ) :
              w'.1.adicCompletion L) = 1 ∧
            HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w' ∈
              w'.1.adicCompletionIntegers L) →
        Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) :
            w.1.adicCompletion L) ^ 2 =
          Valued.v (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ) ^ (k + 2 * j) →
        TwistedUnipotentTerm.wordIndicator K L v w n rT z k j
            (TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x) =
          (W k (2 * (WithZero.log (Valued.v
            (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w))).toNat) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_TwistedUnipotentTerm_wordIndicator_semiLocalCentral_mul_semiLocalUnipotent_eq_walkCount.solution
