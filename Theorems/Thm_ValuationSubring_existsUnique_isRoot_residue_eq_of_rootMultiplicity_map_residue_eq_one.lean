import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one

open Polynomial
theorem ValuationSubring.existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one
    {K : Type*} [Field K] (A : ValuationSubring K) (g : Polynomial A)
    (hsplit : (g.map (algebraMap A K)).Splits)
    (b : IsLocalRing.ResidueField A) (hb : (g.map (IsLocalRing.residue A)).rootMultiplicity b = 1) :
    ∃! r : K, (g.map (algebraMap A K)).IsRoot r ∧ ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one.solution
