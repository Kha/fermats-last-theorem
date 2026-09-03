import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule
import P2M.Util
import P2M.Sol.S_MazurAdmissible_AdmissibleChain_exists_map_addEquiv

open MazurAdmissible

theorem MazurAdmissible.AdmissibleChain.exists_map_addEquiv
    {M : Type*} [AddCommGroup M] {M' : Type*} [AddCommGroup M']
    {p : ℕ} {Φ : OpenAction M} {Φ' : OpenAction M'} (e : M ≃+ M')
    (he : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : M), Φ'.φ σ (e x) = e (Φ.φ σ x))
    (c : AdmissibleChain p Φ) :
    ∃ c' : AdmissibleChain p Φ', filtAlpha c' = filtAlpha c ∧ filtLength c' = filtLength c := by p2m_exact_reverting @_root_.P2MW.S_MazurAdmissible_AdmissibleChain_exists_map_addEquiv.solution
