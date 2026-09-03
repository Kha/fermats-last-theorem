import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq

set_option autoImplicit false
open scoped MatrixGroups ModularForm

theorem CuspForm.exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    (∀ γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)),
        ∃ γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker),
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
          (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ∧
    (∀ γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker),
        ∃ γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)),
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
          (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ∧
    ∃ L : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2 ≃ₗ[ℂ]
        CuspForm (CohCarrier.GammaH (q ^ 2 * M')
          (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker) 2,
      (∀ F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2,
          ⇑(L F) = (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) ∧
      ∀ (γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)))
        (γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker)),
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 →
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 →
        (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 →
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 →
          ∀ F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2,
            ModularCurve.periodOf _ γ' (L F) = ModularCurve.periodOf (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) γ F := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq.solution
