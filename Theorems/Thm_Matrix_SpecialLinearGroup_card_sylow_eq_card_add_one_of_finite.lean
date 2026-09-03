import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite
attribute [-simp] ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe

set_option autoImplicit false

open Matrix MatrixGroups

theorem Matrix.SpecialLinearGroup.card_sylow_eq_card_add_one_of_finite
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (G : Subgroup SL(2, K)) [Finite G] (P : Sylow p G)
    (hq : 3 < Nat.card P) (hP : Nat.card (Sylow p G) ≠ 1) :
    Nat.card (Sylow p G) = Nat.card P + 1 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite.solution
