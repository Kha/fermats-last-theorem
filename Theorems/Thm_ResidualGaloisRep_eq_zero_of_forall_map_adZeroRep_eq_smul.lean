import Definitions.Def_GaloisRep_AdZero
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_eq_zero_of_forall_map_adZeroRep_eq_smul

set_option autoImplicit false

theorem ResidualGaloisRep.eq_zero_of_forall_map_adZeroRep_eq_smul
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* kˣ)
    (φ : LinearMap.ker (LinearMap.trace k ρbar.V) →ₗ[k] k)
    (hφ : ∀ σ f, φ (ρbar.adZeroRep σ f) = ((χ σ : kˣ) : k) • φ f) :
    φ = 0 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_eq_zero_of_forall_map_adZeroRep_eq_smul.solution
