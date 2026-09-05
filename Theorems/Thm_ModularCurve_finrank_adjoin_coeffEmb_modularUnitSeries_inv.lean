module

public import Mathlib
public import Definitions.Def_ModularCurve_LevelOneProlongationPair
public import Definitions.Def_ModularCurve_ModularUnit
public import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_coeffEmb_modularUnitSeries_inv

@[expose] public section
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing
theorem ModularCurve.finrank_adjoin_coeffEmb_modularUnitSeries_inv {q : ℕ} [Fact q.Prime] :
    Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({((⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))))⁻¹} : Set ↥(modularFunctionFieldBar (1 * q))))
      ↥(modularFunctionFieldBar (1 * q)) = q - 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_coeffEmb_modularUnitSeries_inv.solution
