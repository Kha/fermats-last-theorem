import Definitions.Def_IharaMennickeCarrier
import P2M.Util
import P2M.Sol.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul

open scoped MatrixGroups
theorem Ihara.mennickeQ_le_commutator_sup_mennickeQ_mul (q : ℕ) [NeZero q] (m' m'' : ℕ) [NeZero m']
    [NeZero m''] (hcop : Nat.Coprime m' m'') (hm'q : Nat.Coprime m' q) (hm''q : Nat.Coprime m'' q)
    (hmq : Nat.Coprime (m' * m'') q) (hm'n : Nat.Coprime m' (q ^ 2 - 1)) (hsat : q ^ 2 - 1 ∣ m'') :
    Ihara.mennickeQ q m'' ≤ ⁅Ihara.mennickeQ q m'', Ihara.mennickeQ q m''⁆ ⊔ Ihara.mennickeQ q (m' * m'') := by p2m_exact_reverting @_root_.P2MW.S_Ihara_mennickeQ_le_commutator_sup_mennickeQ_mul.solution
