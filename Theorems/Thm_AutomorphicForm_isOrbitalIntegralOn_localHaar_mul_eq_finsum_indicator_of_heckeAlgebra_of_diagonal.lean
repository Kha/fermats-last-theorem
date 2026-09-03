import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem AutomorphicForm.isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (α β : (v.adicCompletion K)ˣ) (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ)
    (mτ : ℝ)
    (hmτ : τ (Subtype.val ⁻¹' (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
      Set (GL (Fin 2) (v.adicCompletion K)))) = ENNReal.ofReal mτ)
    (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) I) :
    (mτ : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) * I =
      ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸
          LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
        Set.indicator
          {c : GL (Fin 2) (v.adicCompletion K) ⧸
              LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
            ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = (α : v.adicCompletion K) ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = (β : v.adicCompletion K)}
          (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal.solution
