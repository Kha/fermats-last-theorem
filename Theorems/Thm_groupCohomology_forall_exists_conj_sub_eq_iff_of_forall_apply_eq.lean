import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_forall_exists_conj_sub_eq_iff_of_forall_apply_eq

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.forall_exists_conj_sub_eq_iff_of_forall_apply_eq
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G)
    (htriv : ∀ s ∈ S, ∀ v : A, A.ρ s v = v) (c : cocycles₁ (Rep.res S.subtype A)) :
    (∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
        A.ρ g (c t) - c s = A.ρ (s : G) a - a) ↔
      ∀ (g : G) (s t : S), (g⁻¹ * s * g : G) = t → A.ρ g (c t) = c s := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_forall_exists_conj_sub_eq_iff_of_forall_apply_eq.solution
