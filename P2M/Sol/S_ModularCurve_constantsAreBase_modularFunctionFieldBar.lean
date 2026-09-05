module

public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_AlgebraicCurve_AdelicIndex
public import Definitions.Def_ModularCurve_JqCoeff
public import Definitions.Def_ModularCurve_QAdicPlace
public import Theorems.Thm_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional
public import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
public import Theorems.Thm_ModularCurve_functionFieldGeneration
public import Theorems.Thm_ModularCurve_order_jqModC
public import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
public import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_constantsAreBase_modularFunctionFieldBar

set_option autoImplicit false

noncomputable section

open IntermediateField

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "HasPrincipalDivisors ConstantsAreBase constantsAreBase_of_deg_eq_one"
p2m_open "AlgebraicCurve~IsCurveOver"

namespace RCAB

open ModularCurve

private theorem constantsAreBase_of_mem (K : Type*) [Field K] (E : IntermediateField K (LaurentSeries K))
    [HasPrincipalDivisors K E] {j : LaurentSeries K} (hjE : j ∈ E) (hj : j.order = -1) :
    ConstantsAreBase K E :=
  have h : ∃ x : E, (qSeriesBar K E x).order = -1 := ⟨⟨j, hjE⟩, hj⟩
  constantsAreBase_of_deg_eq_one (qInftyPlaceBar K E h) (deg_qInftyPlaceBar K h)

private theorem constantsAreBase_laurentBaseChange (L : Type*) [Field L] {instQL : Algebra ℚ L}
    (N : ℕ) [NeZero N] : ConstantsAreBase L (laurentBaseChange L (modularFunctionFieldFull N)) := by
  haveI := hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional L N
  have hmem : jqModC L ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
    rw [laurentBaseChange_adjoin_pair L N (functionFieldGeneration N)]
    exact jqModC_mem L N
  exact constantsAreBase_of_mem L _ hmem (order_jqModC L)

end RCAB

end AlgebraicCurve

end

p2m_open "ModularCurve AlgebraicCurve~IsCurveOver P2MW.S_ModularCurve_constantsAreBase_modularFunctionFieldBar.AlgebraicCurve"

theorem solution (N : ℕ) [NeZero N] :
    ConstantsAreBase (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  AlgebraicCurve.RCAB.constantsAreBase_laurentBaseChange (AlgebraicClosure ℚ) N

example : ∀ (N : ℕ) [NeZero N], ConstantsAreBase (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := @solution

