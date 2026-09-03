import Mathlib
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_GlobalGaloisRep_IsUnramifiedAt_exists_apply_eq_apply_conj_of_isFrobeniusAt

theorem GlobalGaloisRep.IsUnramifiedAt.exists_apply_eq_apply_conj_of_isFrobeniusAt
    {G : Type*} [Group G] {ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G} {q : ℕ}
    (hq : q.Prime) (hunr : GlobalGaloisRep.IsUnramifiedAt ρ q)
    {A A' : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q) (hA' : A'.LiesOverPrime q)
    {σ σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : A.IsFrobeniusAt σ q) (hσ' : A'.IsFrobeniusAt σ' q) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ' = ρ (τ * σ * τ⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_GlobalGaloisRep_IsUnramifiedAt_exists_apply_eq_apply_conj_of_isFrobeniusAt.solution
