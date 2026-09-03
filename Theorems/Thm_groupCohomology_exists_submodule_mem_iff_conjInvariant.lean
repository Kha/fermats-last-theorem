import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_submodule_mem_iff_conjInvariant

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
theorem groupCohomology.exists_submodule_mem_iff_conjInvariant
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G) :
    ∃ V : Submodule k (H1 (Rep.res S.subtype A)), ∀ x, x ∈ V ↔
      ∃ c : cocycles₁ (Rep.res S.subtype A), H1π _ c = x ∧
        ∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
          A.ρ g (c t) - c s = A.ρ (s : G) a - a := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_submodule_mem_iff_conjInvariant.solution
