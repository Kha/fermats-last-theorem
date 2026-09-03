import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_LanglandsTunnell_DetDictionaryRow
import Definitions.Def_ModularForm_EisensteinChiNegThree
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow
attribute [-instance] LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem LanglandsTunnell.liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (H : Subgroup (L ≃ₐ[ℚ] L))
    (hdet : DetDictionaryRow e) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(FixedPoints.intermediateField H : IntermediateField ℚ L))), ∀ v ∉ S,
      (P2.liftTraceSeed e H).b v = ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow.solution
