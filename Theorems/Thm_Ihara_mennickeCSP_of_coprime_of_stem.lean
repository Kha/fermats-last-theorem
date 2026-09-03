import Definitions.Def_IharaMennickeCarrier
import Definitions.Def_SchurMultiplierTrivial
import P2M.Util
import P2M.Sol.S_Ihara_mennickeCSP_of_coprime_of_stem

open scoped MatrixGroups
theorem Ihara.mennickeCSP_of_coprime_of_stem (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q)
    (hcop : Nat.Coprime m (q ^ 2 - 1))
    (hhabel : Ihara.principalCongruenceAway m q hmq
      ≤ commutator (SL(2, Ihara.ZAway q)) ⊔ Ihara.mennickeQ q m)
    (hsurj : Function.Surjective (Ihara.slAwayReduction m q hmq))
    (hstem : Ihara.HasTrivialSchurMultiplier (SL(2, ZMod m))) :
    Ihara.MennickeCSP m q hmq := by p2m_exact_reverting @_root_.P2MW.S_Ihara_mennickeCSP_of_coprime_of_stem.solution
