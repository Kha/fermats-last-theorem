import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_finite_H2_and_natCard_H2_le

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology Rep
theorem groupCohomology.finite_H2_and_natCard_H2_le
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 (Rep.res S.subtype A))]
    [Finite (H2 (A.quotientToInvariants S))] [Finite (H2 (Rep.res S.subtype A))] :
    Finite (H2 A) ∧
      Nat.card (H2 A) ≤ Nat.card (H2 (A.quotientToInvariants S)) * Nat.card (H2 (Rep.res S.subtype A)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finite_H2_and_natCard_H2_le.solution
