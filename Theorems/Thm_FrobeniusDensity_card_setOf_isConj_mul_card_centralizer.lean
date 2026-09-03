import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer

theorem FrobeniusDensity.card_setOf_isConj_mul_card_centralizer {G : Type*} [Group G] (σ : G) :
    Nat.card {τ : G | IsConj σ τ} * Nat.card (Subgroup.centralizer ({σ} : Set G)) = Nat.card G := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer.solution
