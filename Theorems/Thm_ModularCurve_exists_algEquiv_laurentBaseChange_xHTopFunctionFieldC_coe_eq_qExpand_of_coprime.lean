import Mathlib
import Definitions.Def_ModularCurve_XH
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (t : ℕ) [NeZero t] (htM : Nat.Coprime t M) :
    ∃ w : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t)) ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t)),
      ∀ x : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t)),
        (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ ModularCurve.xHFunctionFieldBar M H →
          ((w x : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t))) :
              LaurentSeries (AlgebraicClosure ℚ)) =
            ModularCurve.qExpand (AlgebraicClosure ℚ) t (x : LaurentSeries (AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.solution
