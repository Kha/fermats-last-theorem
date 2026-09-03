import Definitions.Def_ModularCurve_PlaceSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_spPic0_inertia_smul

open AlgebraicCurve ModularCurve
theorem ModularCurve.PlaceSpecialization.spPic0_inertia_smul {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    (S : PlaceSpecialization A ℓ N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : JZero N) : S.spPic0 (σ • x) = S.spPic0 x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_spPic0_inertia_smul.solution
