import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    [Subsingleton (H1 X.X₁)] [Subsingleton (H2 X.X₁)] [Finite X.X₃] :
    Finite (H1 X.X₂) ∧ Finite (H2 X.X₂) ∧ Nat.card (H1 X.X₂) = Nat.card (H2 X.X₂) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite.solution
