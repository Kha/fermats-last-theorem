import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_exists_finite_quotient_and_even_vdet_of_mem

set_option autoImplicit false

open scoped MatrixGroups

theorem CerednikDrinfeld.FormalOmega.exists_finite_quotient_and_even_vdet_of_mem

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))
    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))

    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ'.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal) (hNidx : N.relIndex (Γ'.map ρ) ≠ 0) :
    ∃ (G₂ : Type) (_ : Group G₂) (_ : Finite G₂) (θ : ↥Γ →* G₂),
      Function.Surjective θ ∧ (∀ γ : ↥Γ, θ γ = 1 ↔ ρ (γ : G) ∈ N) ∧
      (∀ γ : ↥Γ, ρ (γ : G) ∈ N → Even (Multiplicative.toAdd (vdet (σ (γ : G))))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_exists_finite_quotient_and_even_vdet_of_mem.solution
