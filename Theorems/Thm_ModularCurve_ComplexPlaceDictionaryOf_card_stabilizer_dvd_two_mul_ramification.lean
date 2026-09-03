import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import P2M.Util
import P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_card_stabilizer_dvd_two_mul_ramification

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.ComplexPlaceDictionaryOf.card_stabilizer_dvd_two_mul_ramification
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) (τ : UpperHalfPlane) :
    Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) ∣
      2 * D.ramification τ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_card_stabilizer_dvd_two_mul_ramification.solution
