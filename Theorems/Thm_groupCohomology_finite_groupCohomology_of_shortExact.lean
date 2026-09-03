import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_finite_groupCohomology_of_shortExact

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.finite_groupCohomology_of_shortExact
    {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ)
    [Finite (groupCohomology X.X₁ n)] [Finite (groupCohomology X.X₃ n)] :
    Finite (groupCohomology X.X₂ n) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finite_groupCohomology_of_shortExact.solution
