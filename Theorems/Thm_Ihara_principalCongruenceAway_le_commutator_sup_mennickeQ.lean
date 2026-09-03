import Definitions.Def_IharaMennickeCarrier
import P2M.Util
import P2M.Sol.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ

open scoped MatrixGroups
theorem Ihara.principalCongruenceAway_le_commutator_sup_mennickeQ (m q : ℕ) [NeZero q]
    (hmq : Nat.Coprime m q) :
    Ihara.principalCongruenceAway m q hmq ≤ commutator SL(2, Ihara.ZAway q) ⊔ Ihara.mennickeQ q m := by p2m_exact_reverting @_root_.P2MW.S_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ.solution
