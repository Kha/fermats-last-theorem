import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule
import P2M.Util
import P2M.Sol.S_MazurAdmissible_exists_admissibleChain_filtAlpha_eq_add

open MazurAdmissible
theorem MazurAdmissible.exists_admissibleChain_filtAlpha_eq_add
    {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) (Φ : OpenAction M)
    (N : AddSubgroup M) (hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ N, Φ.φ σ x ∈ N)
    (ΦN : OpenAction ↥N) (hΦN : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥N), (ΦN.φ σ x : M) = Φ.φ σ x)
    (ΦQ : OpenAction (M ⧸ N))
    (hΦQ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M), ΦQ.φ σ (QuotientAddGroup.mk x) = QuotientAddGroup.mk (Φ.φ σ x))
    (cN : AdmissibleChain q ΦN) (cQ : AdmissibleChain q ΦQ) :
    ∃ c : AdmissibleChain q Φ,
      filtAlpha c = filtAlpha cN + filtAlpha cQ ∧ filtLength c = filtLength cN + filtLength cQ := by p2m_exact_reverting @_root_.P2MW.S_MazurAdmissible_exists_admissibleChain_filtAlpha_eq_add.solution
