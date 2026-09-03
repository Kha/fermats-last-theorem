import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    ∃ κ : ℝ, 0 < κ ∧ ∀ Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ,
      Measurable Φ → Integrable Φ (AutomorphicForm.semiLocalHaar K L v) →
      ∫ g, Φ g ∂(AutomorphicForm.semiLocalHaar K L v) =
        (κ : ℂ) * ∫ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
          (if h : IsUnit p.1 ∧ IsUnit p.2 then
            ((‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ : ℝ) : ℂ) *
              ∫ ξ : (L ⊗[K] v.adicCompletion K), ∫ k in AutomorphicForm.semiLocalIntegralSet K L v,
                Φ (diagUnits2 h.1.unit h.2.unit * AutomorphicForm.unipotentGL2 ξ * k)
                ∂(AutomorphicForm.semiLocalHaar K L v) ∂ν
           else 0) ∂(ν.prod ν) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_forall_integral_semiLocalHaar_eq_mul_integral_integral_setIntegral_iwasawa.solution
