import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_NodeLocalized_exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.NodeLocalized.exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (h₀ : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (y₁ : LaurentSeries A)
    (hy₁ : coeffMap A.subtype y₁ ∈ modularFunctionFieldBar N)
    (hred : coeffMap (NodeLocalized.redRestrict red K) h₀ = coeffMap red y₁)
    (hint :
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) (⟨coeffMap A.subtype y₁, hy₁⟩ : ↥(modularFunctionFieldBar N))) :
    ∃ (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g : ↥(modularFunctionFieldBar N)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver N K ∧
      coeffMap (NodeLocalized.coeffSubring A K).subtype y = (g : LaurentSeries (AlgebraicClosure ℚ)) ∧
      coeffMap (NodeLocalized.redRestrict red K) h₀ = coeffMap (NodeLocalized.redRestrict red K) y ∧
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_NodeLocalized_exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral.solution
