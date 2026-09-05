import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import P2M.Sol.S_ModularCurve_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import P2M.Util
namespace P2MW.S_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem solution (N : ℕ) [NeZero N] :
    modularFunctionFieldBar N = modularFunctionFieldC (AlgebraicClosure ℚ) N := by

  show laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      = modularFunctionFieldC (AlgebraicClosure ℚ) N
  rw [ModularCurve.laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N,
      ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
        (AlgebraicClosure ℚ) N]

  first
  | rfl
  | (show IntermediateField.adjoin (AlgebraicClosure ℚ)
        {x : LaurentSeries (AlgebraicClosure ℚ) |
          ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = jqNModC (AlgebraicClosure ℚ) d}
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
        (divisorExpansionsC (AlgebraicClosure ℚ) N)
     congr 1
     ext x
     constructor
     · rintro ⟨d, hd, hdN, rfl⟩; exact ⟨d, hd, hdN, rfl⟩
     · rintro ⟨d, hd, hdN, rfl⟩; exact ⟨d, hd, hdN, rfl⟩)
