import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_natCard_H2_mul_of_shortExact

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.natCard_H2_mul_of_shortExact
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    [Finite (H1 X.X₁)] [Finite (H1 X.X₂)] [Finite (H1 X.X₃)]
    [Finite (H2 X.X₁)] [Finite (H2 X.X₂)] [Finite (H2 X.X₃)] :
    Nat.card (H2 X.X₂) * Nat.card (H1 X.X₁) * Nat.card (H1 X.X₃)
      = Nat.card (H1 X.X₂) * Nat.card (H2 X.X₁) * Nat.card (H2 X.X₃) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_natCard_H2_mul_of_shortExact.solution
