import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_AlgebraicCurve_ConstantReduction
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (h : ModularCurve.ReductionInputsQExpModL A Γ) :
    ∃ R : ConstantReduction A
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      R.placeMap = ModularCurve.placeReductionQExpModL h ∧
      R.pic0Map = ModularCurve.reductionQExpModL A Γ ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (hyk : ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
          ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
              ∈ R.integers,
          R.residue ⟨_, hO⟩ = ⟨ModularCurve.coeffMap (IsLocalRing.residue A) y, hyk⟩ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL.solution
