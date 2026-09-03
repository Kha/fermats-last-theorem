import Definitions.Def_IharaMennickeCarrier
import P2M.Util
import P2M.Sol.S_Ihara_exists_principalCongruenceAway_le_of_finiteIndex

set_option autoImplicit false

theorem Ihara.exists_principalCongruenceAway_le_of_finiteIndex {q : ℕ} (hq : q.Prime)
    (K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Ihara.ZAway q))) [K.FiniteIndex] :
    ∃ (M : ℕ) (hMq : Nat.Coprime M q), M ≠ 0 ∧ Ihara.principalCongruenceAway M q hMq ≤ K := by p2m_exact_reverting @_root_.P2MW.S_Ihara_exists_principalCongruenceAway_le_of_finiteIndex.solution
