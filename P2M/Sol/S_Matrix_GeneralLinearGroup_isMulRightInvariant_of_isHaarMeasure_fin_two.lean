import Mathlib
import Theorems.Thm_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one
import P2M.Util
namespace P2MW.S_Matrix_GeneralLinearGroup_isMulRightInvariant_of_isHaarMeasure_fin_two

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure

namespace SolGL2HaarUnimodular

theorem map_mul_right_eq_self
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] (g : GL (Fin 2) F) :
    Measure.map (· * g) μ = μ := by

  rw [isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ,
    ← modularCharacterFun_eq_haarScalarFactor μ g]
  have hΔ : modularCharacterFun g = 1 :=
    Matrix.GeneralLinearGroup.modularCharacter_fin_two_eq_one g
  rw [hΔ, one_smul]

end SolGL2HaarUnimodular

theorem solution
    {F : Type*} [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant :=
  ⟨fun g => SolGL2HaarUnimodular.map_mul_right_eq_self μ g⟩
