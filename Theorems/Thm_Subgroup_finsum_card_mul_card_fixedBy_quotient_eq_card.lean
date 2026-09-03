import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_finsum_card_mul_card_fixedBy_quotient_eq_card

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Subgroup.finsum_card_mul_card_fixedBy_quotient_eq_card (p : ℕ) {G : Type} [Group G] [Finite G]
    (b : Subgroup G → ℤ)
    (hb : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p ∧ H ≤ D then b D else 0) = 1)
    (g : G) (hg : (orderOf g).Coprime p) :
    ∑ᶠ D : Subgroup G, (if IsCyclic D ∧ (Nat.card D).Coprime p
      then (Nat.card D : ℤ) * b D * Nat.card (MulAction.fixedBy (G ⧸ D) g) else 0) = Nat.card G := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_finsum_card_mul_card_fixedBy_quotient_eq_card.solution
