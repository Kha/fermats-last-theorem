import Definitions.Def_CuspForm_ModPForms
import Theorems.Thm_ModPForms_one_mem_modPMod_two_of_exists_prime_dvd_mod_three_eq_two
import Theorems.Thm_ModPForms_mul_mem_modPMod_add
import P2M.Util
namespace P2MW.S_ModPForms_modPMod_le_modPMod_add_two_of_exists_prime_dvd_mod_three_eq_two
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

open ModPForms in
theorem solution (N' : ℕ) [NeZero N']
    (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2) (F : Type) [Field F] [CharP F 3] (k : ℤ) :
    modPMod N' k F ≤ modPMod N' (k + 2) F := by
  intro φ hφ
  simpa using ModPForms.mul_mem_modPMod_add N' k 2 F φ 1 hφ
    (ModPForms.one_mem_modPMod_two_of_exists_prime_dvd_mod_three_eq_two N' hε F)
