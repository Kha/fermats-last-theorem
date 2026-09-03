import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FrobeniusEndo
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card
attribute [-simp] AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero

set_option autoImplicit false

theorem AlgebraicCurve.isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [AlgebraicCurve.IsCurveOver K F]
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    AlgebraicCurve.IsFrobeniusEndo (Nat.card k) φ ∧
      Function.Bijective (AlgebraicCurve.Place.restrictAlong φ hφi) ∧
      ∀ w : AlgebraicCurve.Place K F, AlgebraicCurve.Place.inertiaDegAlong φ hφi w = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isFrobeniusEndo_and_bijective_restrictAlong_of_apply_algebraMap_eq_pow_card.solution
