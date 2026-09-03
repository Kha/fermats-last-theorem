import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_AuxLevel_coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (Kq : IntermediateField L (LaurentSeries L))
    (hKq : Kq = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
    (τq : ↥Kq ≃ₐ[L] ↥Kq)
    (hτq : ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓ) q (q ^ 2 * M')
      (ModularCurve.FullLevel.levelH q M') γ⁻¹ Kq τq)
    (x : ↥Kq) (w : ↥K) (hw : ((w : ↥K) : LaurentSeries L) = ModularCurve.qExpand L ℓ ((x : ↥Kq) : LaurentSeries L)) :
    ((τ w : ↥K) : LaurentSeries L) = ModularCurve.qExpand L ℓ ((τq x : ↥Kq) : LaurentSeries L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_AuxLevel_coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom.solution
