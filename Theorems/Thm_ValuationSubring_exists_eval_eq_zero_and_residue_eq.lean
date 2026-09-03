import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_eval_eq_zero_and_residue_eq

theorem ValuationSubring.exists_eval_eq_zero_and_residue_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (q : Polynomial A) (hq : IsUnit q.leadingCoeff)
    (a₀ : IsLocalRing.ResidueField A)
    (hroot : (q.map (IsLocalRing.residue A)).eval a₀ = 0) :
    ∃ α : A, q.eval α = 0 ∧ IsLocalRing.residue A α = a₀ := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_eval_eq_zero_and_residue_eq.solution
