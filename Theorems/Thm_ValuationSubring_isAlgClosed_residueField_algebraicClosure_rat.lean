module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat

@[expose] public section

open IsLocalRing
theorem ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    IsAlgClosed (ResidueField A) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat.solution
