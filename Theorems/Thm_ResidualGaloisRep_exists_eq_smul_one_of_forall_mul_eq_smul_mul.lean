import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_eq_smul_one_of_forall_mul_eq_smul_mul

set_option autoImplicit false

theorem ResidualGaloisRep.exists_eq_smul_one_of_forall_mul_eq_smul_mul
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* kˣ)
    (Y : Module.End k ρbar.V)
    (hY : ∀ σ, Y * ρbar.ρ σ = ((χ σ : kˣ) : k) • (ρbar.ρ σ * Y)) :
    ∃ c : k, Y = c • (1 : Module.End k ρbar.V) ∧ (χ ≠ 1 → c = 0) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_eq_smul_one_of_forall_mul_eq_smul_mul.solution
