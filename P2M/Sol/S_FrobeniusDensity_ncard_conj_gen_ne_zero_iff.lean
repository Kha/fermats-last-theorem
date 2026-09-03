import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card
import P2M.Util
namespace P2MW.S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff

set_option autoImplicit false

theorem solution {G : Type*} [Group G] [Finite G] (σ τ : G) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard ≠ 0
      ↔ ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) τ := by
  constructor
  · intro hne
    obtain ⟨g, k, hk, hgk⟩ := Set.nonempty_of_ncard_ne_zero hne
    exact ⟨k, hk, isConj_iff.mpr ⟨g, hgk⟩⟩
  · rintro ⟨k, hk, hconj⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    exact Set.ncard_ne_zero_of_mem (a := g) ⟨k, hk, hg⟩ (Set.toFinite _)
