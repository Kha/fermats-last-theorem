import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell.Converse NumberField.TateGlobal
open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (Φ : HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hfib : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ T ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : HeightOneSpectrum (𝓞 ℚ) => ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (ΛS ΛSd : ℂ → ℂ) (ε : ℂ) (N : ℝ)
    (hRS : IsNicePinned
      (rsDatum ℚ SQ Φ.a Φ.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        (twistedGammaR K archR uR aR) (twistedGammaC K archR archC uR aR uC kC)
        (twistedGammaR K (fun w hw => (archR w hw).dual) (fun w hw => -uR w hw) aR)
        (twistedGammaC K (fun w hw => (archR w hw).dual) (fun w hw => (archC w hw).dual)
          (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)))
      ΛS ΛSd ε N) :
    IsNicePinned (twistedDatum K (formalBaseChange ℚ K Φ) T archR archC μ uR aR uC kC) ΛS ΛSd ε N := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_isNicePinned_twistedDatum_formalBaseChange_of_isNicePinned_rsDatum.solution
