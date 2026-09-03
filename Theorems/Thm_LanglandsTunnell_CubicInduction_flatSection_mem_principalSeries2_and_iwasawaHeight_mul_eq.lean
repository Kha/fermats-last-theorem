import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ χ' : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (u : ℂ)
    (hχ'₀ : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χ' 0 a : ℂˣ) : ℂ) = ((χ 0 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ u))
    (hχ'₁ : ∀ a : (p.adicCompletion ℚ)ˣ,
      ((χ' 1 a : ℂˣ) : ℂ) = ((χ 1 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-u)))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ) :

    (fun g : GL (Fin 2) (p.adicCompletion ℚ) => f g *
        (((‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 : ℝ) : ℂ) ^ u)) ∈
        principalSeries2 p χ' ∧

    (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ‖((upperUnipotent2 p x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖((upperUnipotent2 p x * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖((upperUnipotent2 p x * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 =
          ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2) ∧

    (∀ (a : Fin 2 → (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        ‖((diagonal2 p a * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖((diagonal2 p a * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖((diagonal2 p a * g : GL (Fin 2) (p.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 =
          ‖(a 0 : p.adicCompletion ℚ)‖ / ‖(a 1 : p.adicCompletion ℚ)‖ *
            (‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
              max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
                ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2)) ∧

    (∀ (g k : GL (Fin 2) (p.adicCompletion ℚ)), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
        ‖((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖((g * k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 =
          ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2) ∧

    (∀ k : GL (Fin 2) (p.adicCompletion ℚ), k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
        ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2 = 1) ∧

    (∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        0 < ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ /
            max ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖
              ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq.solution
