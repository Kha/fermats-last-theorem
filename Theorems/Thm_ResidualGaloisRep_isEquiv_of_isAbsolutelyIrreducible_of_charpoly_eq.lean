import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.LinearAlgebra.Charpoly.Basic
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq

open Module LinearMap
theorem ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k)
    (h₁ : ρ₁.IsAbsolutelyIrreducible) (h₂ : ρ₂.IsAbsolutelyIrreducible)
    (hcp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly) :
    ρ₁.IsEquiv ρ₂ := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq.solution
