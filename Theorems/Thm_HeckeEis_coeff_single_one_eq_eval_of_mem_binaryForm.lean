import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeff_single_one_eq_eval_of_mem_binaryForm {K : Type*} [CommRing K] {n : ℕ}
    {P : MvPolynomial (Fin 2) K} (hP : P ∈ HeckeEis.BinaryForm K n) :
    MvPolynomial.coeff (Finsupp.single 1 n) P = MvPolynomial.eval ![0, 1] P := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm.solution
