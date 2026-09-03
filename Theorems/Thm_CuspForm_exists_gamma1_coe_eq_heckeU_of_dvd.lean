import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd
    {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓ : ℓ ∣ N) (f : CuspForm (Gamma1 N) k) :
    ∃ U : CuspForm (Gamma1 N) k,
      (⇑U : UpperHalfPlane → ℂ) = ModularForm.heckeU k ℓ ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff U n = ModularFormClass.qCoeff f (ℓ * n)) ∧
      ∀ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε f → CuspForm.HasNebentypus ε U := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd.solution
