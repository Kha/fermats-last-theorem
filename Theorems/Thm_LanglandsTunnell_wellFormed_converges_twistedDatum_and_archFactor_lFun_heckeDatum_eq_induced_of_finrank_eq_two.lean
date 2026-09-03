import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter Polynomial
  LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate M4aHerbrand.GenuineDescent

open scoped Classical in

theorem LanglandsTunnell.wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS₀ : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
    (hram : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1)
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ)
    (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
    (hR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt E μ w (uR w hw) ((aR w hw).val : ℤ))
    (hC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt E μ w (uC w hw) (kC w hw))
    (uR' : ∀ w' : InfinitePlace M, w'.IsReal → ℂ) (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (uC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℂ) (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ)
    (huR' : ∀ w', ∀ hw' : w'.IsReal,
      uR' w' hw' = uR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)))
    (haR' : ∀ w', ∀ hw' : w'.IsReal,
      ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
        (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val)
    (huC' : ∀ w', ∀ hw' : w'.IsComplex,
      uC' w' hw' = if h : (w'.comap (algebraMap E M)).IsReal then uR _ h
        else uC _ (InfinitePlace.not_isReal_iff_isComplex.mp h))
    (hkC' : ∀ w', ∀ hw' : w'.IsComplex,
      (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
        else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs) :
    (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).WellFormed ∧
    (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).Converges ∧
    (∀ s : ℂ,
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').archFactor s =
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).archFactor s ∧
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').archFactorDual s =
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).archFactorDual s) ∧
    (∀ s : ℂ, 1 < s.re →
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').LFun s =
        (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
          (((heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').euler w').eval
            (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) *
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).LFun s ∧
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').LFunDual s =
        (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
          (((heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').dual w').eval
            (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) *
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).LFunDual s) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two.solution
