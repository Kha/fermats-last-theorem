import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff

theorem FrobeniusDensity.ncard_conj_gen_ne_zero_iff {G : Type*} [Group G] [Finite G]
    (σ τ : G) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard ≠ 0
      ↔ ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) τ := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.solution
