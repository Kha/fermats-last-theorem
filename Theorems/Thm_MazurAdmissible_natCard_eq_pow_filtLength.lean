import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule
import P2M.Util
import P2M.Sol.S_MazurAdmissible_natCard_eq_pow_filtLength

open MazurAdmissible
theorem MazurAdmissible.natCard_eq_pow_filtLength
    {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) {Φ : OpenAction M}
    (c : AdmissibleChain q Φ) : Nat.card M = q ^ filtLength c := by p2m_exact_reverting @_root_.P2MW.S_MazurAdmissible_natCard_eq_pow_filtLength.solution
