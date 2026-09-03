import Mathlib
import Definitions.Def_ModularCurve_PlaceWidthChar
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twentyFour_of_j_eq_zero_of_charP_two
import Theorems.Thm_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth
import Theorems.Thm_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
import P2M.Util
namespace P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_mul_jWidthChar

set_option autoImplicit false

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (E : WeierstrassCurve K) [E.IsElliptic] :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) E) = 2 * ModularCurve.jWidthChar p E.j := by
  have hchar : ringChar K = p := ringChar.eq K p
  by_cases hp2 : p = 2
  · subst hp2
    by_cases hj : E.j = 0
    · rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_twentyFour_of_j_eq_zero_of_charP_two E hj]
      simp [ModularCurve.jWidthChar, hj]
    · rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
        (Or.inl hchar) E hj]
      simp [ModularCurve.jWidthChar, hj]
  · by_cases hp3 : p = 3
    · subst hp3
      by_cases hj : E.j = 0
      · rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three E hj]
        simp [ModularCurve.jWidthChar, hj]
      · rw [WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
          (Or.inr hchar) E hj]
        simp [ModularCurve.jWidthChar, hj]
    · rw [ModularCurve.jWidthChar_of_ne hp2 hp3]
      have h2 : ringChar K ≠ 2 := by rw [hchar]; exact hp2
      have h3 : ringChar K ≠ 3 := by rw [hchar]; exact hp3
      exact WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth h2 h3 E
