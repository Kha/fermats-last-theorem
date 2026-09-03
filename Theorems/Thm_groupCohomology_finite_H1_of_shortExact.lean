import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_finite_H1_of_shortExact

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.finite_H1_of_shortExact
    {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    [Finite (H1 X.X₁)] [Finite (H1 X.X₃)] :
    Finite (H1 X.X₂) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finite_H1_of_shortExact.solution
