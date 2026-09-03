import Definitions.Def_ModularCurve_PlaceSpecialization
import P2M.Util
namespace P2MW.S_ModularCurve_PlaceSpecialization_spPic0_inertia_smul

open AlgebraicCurve ModularCurve

theorem solution {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    (S : PlaceSpecialization A ℓ N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : JZero N) : S.spPic0 (σ • x) = S.spPic0 x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk]
  obtain ⟨D₁, hD₁, h₁⟩ := S.spPic0_compat (SemilinearAut.degZeroSMulHom (arithmeticGalois (modularFunctionFieldFull N) σ) D)
  obtain ⟨D₂, hD₂, h₂⟩ := S.spPic0_compat D
  rw [h₁, h₂]
  congr 1
  refine Subtype.ext ?_
  rw [hD₁, hD₂, SemilinearAut.coe_degZeroSMulHom, SemilinearAut.divisor_smul_def,
    ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr ?_
  intro w _
  exact S.d6_inertia σ hσ w
