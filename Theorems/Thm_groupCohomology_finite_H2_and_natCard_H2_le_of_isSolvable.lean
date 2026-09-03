import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_finite_H2_and_natCard_H2_le_of_isSolvable

set_option autoImplicit false

open CategoryTheory groupCohomology
theorem groupCohomology.finite_H2_and_natCard_H2_le_of_isSolvable
    {G : Type} [Group G] [Finite G] [Group.IsSolvable G] (A : Rep.{0} ℤ G)
    (h90 : ∀ (H : Type) [Group H] [Finite H] (φ : H →* G), Function.Injective φ →
      Subsingleton (H1 (Rep.res φ A)))
    (hcyc : ∀ (H : Type) [Group H] [Finite H] (φ : H →* G), Function.Injective φ →
      ∀ (N : Subgroup H) [N.Normal], (Nat.card (H ⧸ N)).Prime →
        Finite (H2 ((Rep.res φ A).quotientToInvariants N)) ∧
          Nat.card (H2 ((Rep.res φ A).quotientToInvariants N)) ≤ Nat.card (H ⧸ N)) :
    Finite (H2 A) ∧ Nat.card (H2 A) ≤ Nat.card G := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finite_H2_and_natCard_H2_le_of_isSolvable.solution
