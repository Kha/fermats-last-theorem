import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.Set.Card
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_ncard_conj_gen_eq_of_orderOf_eq_eight

open scoped Classical in

theorem FrobeniusDensity.ncard_conj_gen_eq_of_orderOf_eq_eight {G : Type*} [Group G] [Finite G]
    (σ τ : G) (h8 : orderOf σ = 8) (h3 : IsConj σ (σ ^ 3)) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard
      = 2 * Nat.card (Subgroup.centralizer ({σ} : Set G)) *
          ((if IsConj σ τ then 1 else 0) + (if IsConj (σ ^ 5) τ then 1 else 0)) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_ncard_conj_gen_eq_of_orderOf_eq_eight.solution
