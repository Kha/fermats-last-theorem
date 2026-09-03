import Definitions.Def_ModularCurve_PlaceSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_spPic0_frobenius_smul_eq

open AlgebraicCurve ModularCurve
theorem ModularCurve.PlaceSpecialization.spPic0_frobenius_smul_eq {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    [IsAlgClosed k] [IsCurveOver k (modularFunctionFieldC k N)]
    (S : PlaceSpecialization A ℓ N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) (x : JZero N) :
    S.spPic0 (σ • x) = frobeniusPushforwardGeomLevelPic0OfIsCurveOver k N data hKr (S.spPic0 x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_spPic0_frobenius_smul_eq.solution
