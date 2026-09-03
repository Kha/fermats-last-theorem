import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer

set_option autoImplicit false

theorem groupCohomology.exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer
    {G : Type} [Group G] [Finite G] {X : Type} [MulAction G X]
    (ν : G → G → X →₀ ℤ)
    (hν : ∀ g h k : G, Finsupp.mapDomain (g • ·) (ν h k) - ν (g * h) k + ν g (h * k) - ν g h = 0)
    (hloc : ∀ x₀ : X, ∃ β : ↥(MulAction.stabilizer G x₀) → ℤ,
      ∀ s t : ↥(MulAction.stabilizer G x₀), ν s t x₀ = β s + β t - β (s * t)) :
    ∃ μ : G → X →₀ ℤ, ∀ g h : G, ν g h = Finsupp.mapDomain (g • ·) (μ h) - μ (g * h) + μ g := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer.solution
