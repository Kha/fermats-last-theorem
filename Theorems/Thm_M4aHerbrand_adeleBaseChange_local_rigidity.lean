import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_M4aHerbrand_adeleBaseChange_local_rigidity
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand

theorem M4aHerbrand.adeleBaseChange_local_rigidity
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    (∀ (a : AdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)),
      ((B.β a).2 : FiniteAdeleRing (𝓞 L) L) w =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom K L
          (⟨w, rfl⟩ : (w.under (𝓞 K)).Extension (𝓞 L))
          ((a.2 : FiniteAdeleRing (𝓞 K) K) (w.under (𝓞 K)))) ∧
    ∀ w : InfinitePlace L, ∃ (v : InfinitePlace K) (θ : ℂ ≃+* ℂ), ∀ a : AdeleRing (𝓞 K) K,
      InfinitePlace.Completion.extensionEmbedding w (((B.β a).1 : InfiniteAdeleRing L) w) =
        θ (InfinitePlace.Completion.extensionEmbedding v ((a.1 : InfiniteAdeleRing K) v)) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_adeleBaseChange_local_rigidity.solution
