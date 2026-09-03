import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
    (L : Type) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) (hj : Transcendental ℚ j)
    [FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set ↥F₀)) ↥F₀]
    (jb : ↥(laurentBaseChange L F₀))
    (hjb : (jb : LaurentSeries L) = coeffEmb L ((j : ↥F₀) : LaurentSeries ℚ)) :
    Transcendental L jb ∧
      FiniteDimensional ↥(IntermediateField.adjoin L ({jb} : Set ↥(laurentBaseChange L F₀)))
        ↥(laurentBaseChange L F₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb.solution
