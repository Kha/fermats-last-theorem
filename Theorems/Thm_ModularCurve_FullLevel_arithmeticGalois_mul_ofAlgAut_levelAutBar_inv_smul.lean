import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_inv_smul

set_option autoImplicit false

open ModularCurve open ModularCurve.FullLevel hiding levelAutInputs_of_not_dvd open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_inv_smul
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ *
        SemilinearAut.ofAlgAut (levelAutBar q M' (σ⁻¹ • ζ) γ) =
      SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ) *
        arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_inv_smul.solution
