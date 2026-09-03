import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_finite_H2_of_shortExact

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.finite_H2_of_shortExact
    {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    [Finite (H2 X.X₁)] [Finite (H2 X.X₃)] :
    Finite (H2 X.X₂) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finite_H2_of_shortExact.solution
