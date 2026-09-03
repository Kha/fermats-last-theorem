import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_tameCharacter_conj_of_isFrobeniusAt

theorem ValuationSubring.tameCharacter_conj_of_isFrobeniusAt
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ) {m p : ℕ} (hm : 0 < m)
    (hπ : π ^ m = p) {φ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : P.IsFrobeniusAt φ p)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π (φ * σ * φ⁻¹) = P.tameCharacter π σ ^ p := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_tameCharacter_conj_of_isFrobeniusAt.solution
