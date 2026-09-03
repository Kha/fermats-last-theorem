import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_linearEquiv_H1_of_forall_iff_of_isUnit_index

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.exists_linearEquiv_H1_of_forall_iff_of_isUnit_index
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    [S.FiniteIndex] (hindex : IsUnit ((S.index : k)))
    (V : Submodule k (H1 (Rep.res S.subtype A)))
    (hV : ∀ x, x ∈ V ↔ ∃ c : cocycles₁ (Rep.res S.subtype A), H1π _ c = x ∧
      ∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
        A.ρ g (c t) - c s = A.ρ (s : G) a - a) :
    ∃ e : H1 A ≃ₗ[k] V, ∀ y : H1 A,
      ((e y : V) : H1 (Rep.res S.subtype A)) = (H1InfRes A S).g.hom y := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_linearEquiv_H1_of_forall_iff_of_isUnit_index.solution
