import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_cocycles1_restrict_eq_add_of_isUnit_index

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.exists_cocycles1_restrict_eq_add_of_isUnit_index
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    [S.FiniteIndex] (hindex : IsUnit ((S.index : k)))
    (c : cocycles₁ (Rep.res S.subtype A))
    (hc : ∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
      A.ρ g (c t) - c s = A.ρ (s : G) a - a) :
    ∃ (c' : cocycles₁ A) (a : A), ∀ s : S, c' (s : G) = c s + (A.ρ (s : G) a - a) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_cocycles1_restrict_eq_add_of_isUnit_index.solution
