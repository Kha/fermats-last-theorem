import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule
import P2M.Util
import P2M.Sol.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup
open MazurAdmissible
theorem MazurAdmissible.AdmissibleChain.nonempty_of_addSubgroup
    {M : Type*} [AddCommGroup M] {p : ℕ} (hp : p.Prime) (Φ : OpenAction M)
    (N : AddSubgroup M)
    (hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ N, Φ.φ σ x ∈ N)
    (ΦN : OpenAction ↥N)
    (hΦN : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥N), (ΦN.φ σ x : M) = Φ.φ σ x)
    (c : AdmissibleChain p Φ) :
    Nonempty (AdmissibleChain p ΦN) := by p2m_exact_reverting @_root_.P2MW.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup.solution
