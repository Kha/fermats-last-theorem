import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_heckeAlphaBar_mem_nodeIntegersOver_and_nodeResidue_eq_coeffMap
attribute [-instance] ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.heckeAlphaBar_mem_nodeIntegersOver_and_nodeResidue_eq_coeffMap
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g : ↥(modularFunctionFieldBar N))
    (hgy : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap (NodeLocalized.coeffSubring A K).subtype y)
    (hgK : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver N K)
    (hint : IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) g) :
    (∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q g ∈ R.nodeIntegersOver K w,
      ((R.nodeResidue₁ w ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q g, h.1⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
        = coeffMap (NodeLocalized.redRestrict red K) y) ∧
    (∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q g ∈ R.nodeIntegersOver K w,
      ((R.nodeResidue₂ w ⟨heckeBetaBar (AlgebraicClosure ℚ) N q g, h.1⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
        = coeffMap (NodeLocalized.redRestrict red K) y) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_heckeAlphaBar_mem_nodeIntegersOver_and_nodeResidue_eq_coeffMap.solution
