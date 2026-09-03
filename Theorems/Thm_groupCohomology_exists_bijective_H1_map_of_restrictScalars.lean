import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_bijective_H1_map_of_restrictScalars

set_option autoImplicit false

open groupCohomology

universe u

theorem groupCohomology.exists_bijective_H1_map_of_restrictScalars
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : Type u} [Group G]
    {V : Type u} [AddCommGroup V] [Module K V] [Module k V] [IsScalarTower k K V]
    (ρ : Representation K G V) (ρ₀ : Representation k G V)
    (hρ : ∀ g v, ρ₀ g v = ρ g v) :
    ∃ Ψ : H1 (Rep.of ρ₀) →ₛₗ[algebraMap k K] H1 (Rep.of ρ),
      Function.Bijective Ψ ∧
      (∀ (c₀ : cocycles₁ (Rep.of ρ₀)) (c : cocycles₁ (Rep.of ρ)), (c₀ : G → V) = c →
        Ψ (H1π (Rep.of ρ₀) c₀) = H1π (Rep.of ρ) c) ∧
      (∀ [FiniteDimensional k K], ∀ X : Submodule K (H1 (Rep.of ρ)),
        Module.finrank k (X.comap Ψ) = Module.finrank k K * Module.finrank K X) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_bijective_H1_map_of_restrictScalars.solution
