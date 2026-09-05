module

public import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import Definitions.Def_ModularCurve_X0

namespace P2MW.S_ModularCurve_laurentBaseChange_adjoin

open ModularCurve IntermediateField Polynomial

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (S : Set (LaurentSeries ℚ)) : ModularCurve.laurentBaseChange L (IntermediateField.adjoin ℚ S) = IntermediateField.adjoin L (ModularCurve.coeffEmb L '' S) := by
  apply le_antisymm
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hle : (IntermediateField.adjoin ℚ S).toSubfield ≤
        (IntermediateField.adjoin L (coeffEmb L '' S)).toSubfield.comap (coeffEmb L) := by
      rw [IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.mpr ?_
      rintro x (⟨c, rfl⟩ | hx)
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        have : coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c)
            = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
          rw [algebraMap_apply_eq_single, coeffEmb, coeffMap_single,
            ← algebraMap_laurentSeries_eq_single]
        rw [this]
        exact (IntermediateField.adjoin L (coeffEmb L '' S)).algebraMap_mem _
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        exact IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩
    exact hle hy
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange L (IntermediateField.subset_adjoin ℚ S hy)
end S_ModularCurve_laurentBaseChange_adjoin
end P2MW

public section
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

theorem ModularCurve.laurentBaseChange_adjoin (L : Type*) [Field L] [Algebra ℚ L] (S : Set (LaurentSeries ℚ)) : ModularCurve.laurentBaseChange L (IntermediateField.adjoin ℚ S) = IntermediateField.adjoin L (ModularCurve.coeffEmb L '' S) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentBaseChange_adjoin.solution
end
