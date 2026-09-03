import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_kroneckerCentreDichotomy
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve AlgebraicCurve
theorem ModularCurve.kroneckerCentreDichotomy
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (hKR : IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jqN ℓ - jq ^ ℓ) * qExpand ℚ N (jq - (jqN ℓ) ^ ℓ)))
      ∧ IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jq - (jqN ℓ) ^ ℓ) * qExpand ℚ N (jqN ℓ - jq ^ ℓ))))
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))
    (aj aN bj bN : A)
    (haj : 0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (aj : AlgebraicClosure ℚ)))
    (haN : 0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (aN : AlgebraicClosure ℚ)))
    (hbj : 0 < (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (bj : AlgebraicClosure ℚ)))
    (hbN : 0 < (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (bN : AlgebraicClosure ℚ))) :
    (red aj = red bj ^ ℓ ∧ red aN = red bN ^ ℓ)
      ∨ (red aj ^ ℓ = red bj ∧ red aN ^ ℓ = red bN) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_kroneckerCentreDichotomy.solution
