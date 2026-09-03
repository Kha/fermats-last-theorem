import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_isOfFinOrder_units_residueField_of_liesOverPrime
set_option autoImplicit false
theorem ValuationSubring.isOfFinOrder_units_residueField_of_liesOverPrime (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (u : (IsLocalRing.ResidueField ↥A)ˣ) : IsOfFinOrder u := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isOfFinOrder_units_residueField_of_liesOverPrime.solution
