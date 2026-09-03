import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_nonempty_ringHom_residueField_of_finite_of_charP
set_option autoImplicit false

theorem ValuationSubring.nonempty_ringHom_residueField_of_finite_of_charP
    (p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (k : Type) [Field k] [Finite k] [CharP k p] :
    Nonempty (k →+* IsLocalRing.ResidueField P) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_nonempty_ringHom_residueField_of_finite_of_charP.solution
