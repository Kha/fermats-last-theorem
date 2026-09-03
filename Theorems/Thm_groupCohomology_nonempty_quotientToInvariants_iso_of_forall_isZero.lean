import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_nonempty_quotientToInvariants_iso_of_forall_isZero

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology Rep
theorem groupCohomology.nonempty_quotientToInvariants_iso_of_forall_isZero {k G : Type u} [CommRing k] [Group G]
    (N : Subgroup G) [N.Normal] (A : Rep.{u} k G)
    (hN : ∀ i : ℕ, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res N.subtype A) (i + 1))) (n : ℕ) :
    Nonempty (groupCohomology (A.quotientToInvariants N) (n + 1) ≅ groupCohomology A (n + 1)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_nonempty_quotientToInvariants_iso_of_forall_isZero.solution
