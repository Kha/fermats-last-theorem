import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant
import P2M.Util
namespace P2MW.S_NumberField_IdeleLocalInv_hasLocalInv_iff_of_forall_map_prG_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (z : (AdeleRing (𝓞 K) K)ˣ), g • z = D.unitsAct g z)
    (x₁ x₂ : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (hx : ∀ (w : HeightOneSpectrum (𝓞 K))
      (prG : Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ),
      (∀ z : (AdeleRing (𝓞 K) K)ˣ, prG.hom (Additive.ofMul z) = Additive.ofMul (finPart w z)) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype prG 2).hom x₁
        = (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype prG 2).hom x₂)
    (v : HeightOneSpectrum (𝓞 E)) (t : AddCircle (1 : ℚ)) :
    NumberField.IdeleLocalInv.HasLocalInv E K D hactI x₁ v t ↔ NumberField.IdeleLocalInv.HasLocalInv E K D hactI x₂ v t := by
  constructor
  · rintro ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', n, hcoord, ht⟩
    exact ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', n, (hx w (prG w) (hpr w)) ▸ hcoord, ht⟩
  · rintro ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', n, hcoord, ht⟩
    exact ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', n, (hx w (prG w) (hpr w)).symm ▸ hcoord, ht⟩
