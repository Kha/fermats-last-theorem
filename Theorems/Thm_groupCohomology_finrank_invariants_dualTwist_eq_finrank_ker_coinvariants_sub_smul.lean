import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul
    {k G : Type u} [Field k] [Group G] (M : Rep k G) [FiniteDimensional k M]
    (χ : G →* kˣ) (N : Subgroup G) (hχN : ∀ n ∈ N, χ n = 1)
    (φ : G) (hgen : ∀ g, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ N) (a : k) (hχφ : (χ φ : k) = a)

    (D : Type u) [AddCommGroup D] [Module k D] [FiniteDimensional k D]
    (π : M →ₗ[k] D) (hπ : Function.Surjective π)
    (hker : LinearMap.ker π = ⨆ n ∈ N, LinearMap.range (M.ρ n - 1))
    (φD : D →ₗ[k] D) (hφD : φD ∘ₗ π = π ∘ₗ M.ρ φ) :
    finrank k (M.dualTwist χ).ρ.invariants = finrank k (LinearMap.ker (φD - a • 1)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_invariants_dualTwist_eq_finrank_ker_coinvariants_sub_smul.solution
