import Definitions.Def_MazurAdmissible_GaloisModule
import P2M.Util
import P2M.Sol.S_MazurAdmissible_AdmissibleChain_exists_filtAlpha_eq_of_le_filtLength_two

open MazurAdmissible
theorem MazurAdmissible.AdmissibleChain.exists_filtAlpha_eq_of_le_filtLength_two
    {M : Type*} [AddCommGroup M] (Φ : OpenAction M) (c : AdmissibleChain 2 Φ)
    (k : ℕ) (hk : k ≤ filtLength c) :
    ∃ c' : AdmissibleChain 2 Φ, filtLength c' = filtLength c ∧ filtAlpha c' = k := by p2m_exact_reverting @_root_.P2MW.S_MazurAdmissible_AdmissibleChain_exists_filtAlpha_eq_of_le_filtLength_two.solution
