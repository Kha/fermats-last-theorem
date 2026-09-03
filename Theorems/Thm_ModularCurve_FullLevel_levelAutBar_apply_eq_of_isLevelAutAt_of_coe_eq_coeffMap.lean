import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (e : L →+* AlgebraicClosure ℚ)
    (ζ' : ModularCurve.FullLevel.Idx q) (hζ' : ζ'.val = e ζ)
    (ιK : ↥K →+* ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hιK : ∀ x : ↥K, ((ιK x : ↥(ModularCurve.FullLevel.fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.coeffMap e (x : LaurentSeries L))
    (ε : SL(2, ℤ)) (hε : ε ∈ CongruenceSubgroup.Gamma0 M')
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ε K σ)
    (x : ↥K) :
    ιK (σ x) = ModularCurve.FullLevel.levelAutBar q M' ζ' ε (ιK x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap.solution
