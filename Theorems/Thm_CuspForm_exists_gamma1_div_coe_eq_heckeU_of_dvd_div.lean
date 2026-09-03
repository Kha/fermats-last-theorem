import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div
    {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ)
    (ε' : DirichletCharacter ℂ (N / ℓ)) (f : CuspForm (Gamma1 N) k)
    (hf : CuspForm.HasNebentypus
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f) :
    ∃ h : CuspForm (Gamma1 (N / ℓ)) k,
      (⇑h : UpperHalfPlane → ℂ) = ModularForm.heckeU k ℓ ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff h n = ModularFormClass.qCoeff f (ℓ * n)) ∧
      CuspForm.HasNebentypus ε' h := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div.solution
