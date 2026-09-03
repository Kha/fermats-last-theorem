import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_natCard_H2_eq_natCard_of_shortExact_of_iso_trivial

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) (e : X.X₃ ≅ Rep.trivial ℤ G ℤ)
    [Finite (H1 X.X₁)] [Finite (H2 X.X₁)] (h1 : Nat.card (H1 X.X₁) = Nat.card (H2 X.X₁))
    [Subsingleton (H1 X.X₂)] :
    Finite (H2 X.X₂) ∧ Nat.card (H2 X.X₂) = Nat.card G := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_natCard_H2_eq_natCard_of_shortExact_of_iso_trivial.solution
