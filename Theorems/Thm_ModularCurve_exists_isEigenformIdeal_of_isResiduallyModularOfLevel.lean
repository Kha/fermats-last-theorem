import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_ModularCurve_EigenformIdeal
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isEigenformIdeal_of_isResiduallyModularOfLevel
attribute [-instance] CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree
attribute [-simp] CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

theorem ModularCurve.exists_isEigenformIdeal_of_isResiduallyModularOfLevel
    (W : WeierstrassCurve ℤ) {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 0 < N)
    (hmod : W.IsResiduallyModularOfLevel p N) :
    ∃ 𝔪 : Ideal ModularCurve.HeckeAlg, ModularCurve.IsEigenformIdeal N 𝔪 ∧
      (p : ModularCurve.HeckeAlg) ∈ 𝔪 ∧
      ∀ ℓ : Nat.Primes, W.IsGoodPrimeFor ℓ → ¬ (ℓ : ℕ) ∣ N → (ℓ : ℕ) ≠ p →
        ModularCurve.heckeGen ℓ - MvPolynomial.C (W.apOfModel ℓ) ∈ 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isEigenformIdeal_of_isResiduallyModularOfLevel.solution
