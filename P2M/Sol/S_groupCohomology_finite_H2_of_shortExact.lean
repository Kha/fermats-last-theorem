import Mathlib
import Theorems.Thm_groupCohomology_finite_groupCohomology_of_shortExact
import P2M.Util
namespace P2MW.S_groupCohomology_finite_H2_of_shortExact

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
open Rep.FiniteCyclicGroup

theorem solution
    {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    [Finite (H2 X.X₁)] [Finite (H2 X.X₃)] :
    Finite (H2 X.X₂) := by
  exact finite_groupCohomology_of_shortExact hX 2
