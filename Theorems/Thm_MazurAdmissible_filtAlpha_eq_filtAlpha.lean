import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule
import P2M.Util
import P2M.Sol.S_MazurAdmissible_filtAlpha_eq_filtAlpha

open MazurAdmissible
theorem MazurAdmissible.filtAlpha_eq_filtAlpha
    {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Φ : OpenAction M}
    (c c' : AdmissibleChain q Φ) : filtAlpha c = filtAlpha c' := by p2m_exact_reverting @_root_.P2MW.S_MazurAdmissible_filtAlpha_eq_filtAlpha.solution
