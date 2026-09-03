import Definitions.Def_NumberField_AdelicBox
import P2M.Util
namespace P2MW.S_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

namespace P2mSolAdelicBoxHaarOne

theorem main (K : Type) [Field K] [NumberField K]
    [inst : MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)] :
    ∃ μK : Measure (AdeleRing (𝓞 K) K), μK.IsAddHaarMeasure ∧ μK (NumberField.AdelicBox.adelicBox K) = 1 := by

  have hinst : inst = NumberField.AdelicHaar.adeleBorel (𝓞 K) K := BorelSpace.measurable_eq
  subst hinst
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  set μ₀ : Measure (AdeleRing (𝓞 K) K) := Measure.addHaar with hμ₀
  have h0 : μ₀ (NumberField.AdelicBox.adelicBox K) ≠ 0 :=
    (NumberField.AdelicBox.measure_adelicBox_pos K μ₀).ne'
  have htop : μ₀ (NumberField.AdelicBox.adelicBox K) ≠ ⊤ :=
    (NumberField.AdelicBox.measure_adelicBox_lt_top K μ₀).ne
  refine ⟨(μ₀ (NumberField.AdelicBox.adelicBox K))⁻¹ • μ₀, ?_, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr h0)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

end P2mSolAdelicBoxHaarOne

theorem solution (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)] :
    ∃ μK : Measure (AdeleRing (𝓞 K) K), μK.IsAddHaarMeasure ∧ μK (NumberField.AdelicBox.adelicBox K) = 1 :=
  P2mSolAdelicBoxHaarOne.main K
