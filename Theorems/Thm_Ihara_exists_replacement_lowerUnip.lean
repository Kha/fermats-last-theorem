import Definitions.Def_IharaMennickeCarrier
import P2M.Util
import P2M.Sol.S_Ihara_exists_replacement_lowerUnip

set_option autoImplicit false

open scoped MatrixGroups
theorem Ihara.exists_replacement_lowerUnip (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q) (X : SL(2, ZAway q))
    (hX : X ∈ principalCongruenceAway m q hmq)
    (A B : ℤ) (u u' v' : ZAway q) (hu'v' : u' * v' = 1)
    (hα : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 = algebraMap ℤ (ZAway q) A * u)
    (hβ : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 = algebraMap ℤ (ZAway q) B * u') (k : ℤ) :
    ∃ X' : SL(2, ZAway q), X' ∈ principalCongruenceAway m q hmq ∧
      QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X' =
        QuotientGroup.mk' (Subgroup.normalClosure
          ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X ∧
      (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
        algebraMap ℤ (ZAway q) (A + B * (m : ℤ) * k) * u ∧
      (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
        (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 := by p2m_exact_reverting @_root_.P2MW.S_Ihara_exists_replacement_lowerUnip.solution
