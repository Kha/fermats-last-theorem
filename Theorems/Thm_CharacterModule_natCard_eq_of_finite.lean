import Mathlib
import P2M.Util
import P2M.Sol.S_CharacterModule_natCard_eq_of_finite

theorem CharacterModule.natCard_eq_of_finite (M : Type*) [AddCommGroup M] [Finite M] :
    Nat.card (CharacterModule M) = Nat.card M := by p2m_exact_reverting @_root_.P2MW.S_CharacterModule_natCard_eq_of_finite.solution
