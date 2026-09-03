import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_IsConfluentPattern_exists_eq_of_lt_jetMult

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.IsConfluentPattern.exists_eq_of_lt_jetMult
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {M : ℕ} {P : Fin M → Place K F} {t : Fin M → F} {e : Fin M → ℕ}
    (hpat : IsConfluentPattern P t e) (i : Fin M) {q : ℕ} (hq : q < jetMult P (P i)) :
    ∃ i', P i' = P i ∧ e i' = q := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_IsConfluentPattern_exists_eq_of_lt_jetMult.solution
