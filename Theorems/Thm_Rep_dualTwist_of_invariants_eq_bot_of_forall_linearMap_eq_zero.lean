import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import P2M.Util
import P2M.Sol.S_Rep_dualTwist_of_invariants_eq_bot_of_forall_linearMap_eq_zero

set_option autoImplicit false

universe u

theorem Rep.dualTwist_of_invariants_eq_bot_of_forall_linearMap_eq_zero
    {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K]
    {G : Type u} [Group G]
    {V : Type u} [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    [FiniteDimensional K V]
    (ρ : Representation K G V) (ρ₀ : Representation k G V) (hρ : ∀ g v, ρ₀ g v = ρ g v)
    (χ₀ : G →* kˣ)
    (h : ∀ φ : V →ₗ[K] K,
      (∀ g v, φ (ρ g v) = algebraMap k K ((χ₀ g : kˣ) : k) • φ v) → φ = 0) :
    ((Rep.of ρ₀).dualTwist χ₀).ρ.invariants = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Rep_dualTwist_of_invariants_eq_bot_of_forall_linearMap_eq_zero.solution
