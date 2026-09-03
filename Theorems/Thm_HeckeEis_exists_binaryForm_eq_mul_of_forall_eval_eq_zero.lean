import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero

set_option autoImplicit false

open MvPolynomial in

theorem HeckeEis.exists_binaryForm_eq_mul_of_forall_eval_eq_zero (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (n : ℕ) (F : MvPolynomial (Fin 2) K)
    (hF : F ∈ HeckeEis.BinaryForm K n)
    (hvan : ∀ v : Fin 2 → ZMod p,
      MvPolynomial.eval (fun i => ZMod.castHom (dvd_refl p) K (v i)) F = 0) :
    ∃ H : MvPolynomial (Fin 2) K, H ∈ HeckeEis.BinaryForm K (n - (p + 1)) ∧
      F = (X 0 ^ p * X 1 - X 0 * X 1 ^ p) * H := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero.solution
