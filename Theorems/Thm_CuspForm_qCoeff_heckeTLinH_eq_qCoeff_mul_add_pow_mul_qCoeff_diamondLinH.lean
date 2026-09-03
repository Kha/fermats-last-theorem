import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH

set_option autoImplicit false

open scoped ModularForm MatrixGroups

theorem CuspForm.qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(CuspForm.heckeTLinH k hℓ hℓM f)) n =
      ModularFormClass.qCoeff (⇑f) (n * ℓ) +
        (ℓ : ℂ) ^ (k - 1) *
          (if ℓ ∣ n then
            ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH k (CuspForm.unitOfPrimeNotDvd hℓ hℓM) f)) (n / ℓ)
           else 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH.solution
