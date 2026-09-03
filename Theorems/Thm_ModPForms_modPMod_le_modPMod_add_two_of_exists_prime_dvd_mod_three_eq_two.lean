import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_modPMod_le_modPMod_add_two_of_exists_prime_dvd_mod_three_eq_two
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

theorem ModPForms.modPMod_le_modPMod_add_two_of_exists_prime_dvd_mod_three_eq_two (N' : ℕ) [NeZero N']
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2) (F : Type) [Field F] [CharP F 3] (k : ℤ) :
    modPMod N' k F ≤ modPMod N' (k + 2) F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_modPMod_le_modPMod_add_two_of_exists_prime_dvd_mod_three_eq_two.solution
