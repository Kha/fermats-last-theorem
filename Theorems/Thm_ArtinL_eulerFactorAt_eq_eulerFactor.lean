import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import P2M.Util
import P2M.Sol.S_ArtinL_eulerFactorAt_eq_eulerFactor

set_option autoImplicit false

open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem ArtinL.eulerFactorAt_eq_eulerFactor {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ p) :
    (∀ v ∈ ArtinL.inertiaInvariants ρ A,
        Deformation.matrixRepresentation ρ σ v ∈ ArtinL.inertiaInvariants ρ A) ∧
      ArtinL.eulerFactorAt ρ A σ = ArtinL.eulerFactor ρ p := by p2m_exact_reverting @_root_.P2MW.S_ArtinL_eulerFactorAt_eq_eulerFactor.solution
