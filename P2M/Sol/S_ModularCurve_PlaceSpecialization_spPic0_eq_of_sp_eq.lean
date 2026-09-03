import Definitions.Def_ModularCurve_PlaceSpecialization
import P2M.Util
namespace P2MW.S_ModularCurve_PlaceSpecialization_spPic0_eq_of_sp_eq

open AlgebraicCurve ModularCurve

theorem solution {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    (S T : PlaceSpecialization A ℓ N data hKr k red hα hβ) (h : S.sp = T.sp) :
    S.spPic0 = T.spPic0 := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  obtain ⟨D₁, hD₁, hS⟩ := S.spPic0_compat D
  obtain ⟨D₂, hD₂, hT⟩ := T.spPic0_compat D
  rw [hS, hT]
  congr 1
  exact Subtype.ext (by rw [hD₁, hD₂, h])
