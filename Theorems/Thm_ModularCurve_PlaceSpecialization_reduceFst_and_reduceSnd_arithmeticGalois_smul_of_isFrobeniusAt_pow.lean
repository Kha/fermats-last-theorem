import Mathlib
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~arithFrobC_smul_eq_frobOnPlacesGeomLevel ModularCurve.PlaceSpecialization"

theorem ModularCurve.PlaceSpecialization.reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) [IsAlgClosed k]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ) (hσ : A.IsFrobeniusAt σ (q ^ n))
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.reduceFst (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = (arithFrobC q k N) ^ n • P.reduceFst V ∧
    P.reduceSnd (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = (arithFrobC q k N) ^ n • P.reduceSnd V := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_reduceFst_and_reduceSnd_arithmeticGalois_smul_of_isFrobeniusAt_pow.solution
