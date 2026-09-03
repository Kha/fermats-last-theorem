import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_EigenformCoefficientRing
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_exists_parabolicRealization
attribute [-instance] ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open CongruenceSubgroup
theorem ModularCurve.Period.exists_parabolicRealization (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : f.IsNormalizedEigenform)
    (hint : f.PrimeCoeffsIntegral)
    (k : Type) [Field k] (red : integralClosure ℤ ℂ →+* k) :
    ∃ f₀ : ModularCurve.Period.parabolicHoms k (Gamma0 N) k, f₀ ≠ 0 ∧
      ∀ (ℓ : ℕ) (_ : NeZero ℓ) (hℓp : ℓ.Prime),
        HeckeEis.heckeOperatorHom N ℓ k (f₀ : Additive (Gamma0 N) →+ k) =
          (red (CuspForm.eigenLift hint ⟨ℓ, hℓp⟩)) •
            (f₀ : Additive (Gamma0 N) →+ k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_exists_parabolicRealization.solution
