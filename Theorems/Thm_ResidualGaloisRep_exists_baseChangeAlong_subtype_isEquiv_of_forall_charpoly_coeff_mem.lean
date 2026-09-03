import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.LinearAlgebra.Charpoly.Basic
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_baseChangeAlong_subtype_isEquiv_of_forall_charpoly_coeff_mem

theorem ResidualGaloisRep.exists_baseChangeAlong_subtype_isEquiv_of_forall_charpoly_coeff_mem {k : Type} [Field k] (k₀ : Subfield k) [Finite ↥k₀]
    (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (hcoeff : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ i : ℕ,
      (LinearMap.charpoly (ρbar.ρ σ)).coeff i ∈ k₀) :
    ∃ ρ₀ : ResidualGaloisRep ↥k₀,
      (ρ₀.baseChangeAlong k₀.subtype).IsEquiv ρbar := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_baseChangeAlong_subtype_isEquiv_of_forall_charpoly_coeff_mem.solution
