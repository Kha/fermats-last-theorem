import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul

set_option autoImplicit false

theorem groupCohomology.exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul
    {G : Type} [Group G] [Finite G] {X : Type} [MulAction G X]
    (n : G → X →₀ ℤ) (hn : ∀ g h : G, n (g * h) = n g + Finsupp.mapDomain (g • ·) (n h)) :
    ∃ m : X →₀ ℤ, ∀ g : G, n g = m - Finsupp.mapDomain (g • ·) m := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul.solution
