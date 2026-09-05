module

public import Mathlib
public import Definitions.Def_ModularCurve_PlaceSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_red_surjective

@[expose] public section
attribute [-simp] ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve
theorem ModularCurve.PlaceSpecialization.red_surjective
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) : Function.Surjective red := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_red_surjective.solution
