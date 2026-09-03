import Definitions.Def_ModularCurve_PlaceSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_spPic0_eq_of_sp_eq

open AlgebraicCurve ModularCurve
theorem ModularCurve.PlaceSpecialization.spPic0_eq_of_sp_eq {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    (S T : PlaceSpecialization A ℓ N data hKr k red hα hβ) (h : S.sp = T.sp) :
    S.spPic0 = T.spPic0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_spPic0_eq_of_sp_eq.solution
