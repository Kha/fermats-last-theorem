import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackage_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes
set_option autoImplicit false
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve

theorem ModularCurve.DRModelPackage.eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    {k : Type} [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    [IsNoetherianRing ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)]

    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x) :

    (Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom
        (IsLocalRing.maximalIdeal _)).IsPrime ∧
    ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) ∈
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom
        (IsLocalRing.maximalIdeal _) ∧
    (Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom
        (IsLocalRing.maximalIdeal _)).IsPrime ∧
    ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) ∈
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom
        (IsLocalRing.maximalIdeal _) ∧

    (∀ (𝔭 : Ideal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)),
      𝔭 ∈ (Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)}).minimalPrimes →
      𝔭 = Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom
        (IsLocalRing.maximalIdeal _) ∨
      𝔭 = Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom
        (IsLocalRing.maximalIdeal _)) ∧

    (∀ (𝔭 : Ideal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)) [𝔭.IsPrime],
      𝔭.height = 1 →
      ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) ∈ 𝔭 →
      𝔭 = Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom
        (IsLocalRing.maximalIdeal _) ∨
      𝔭 = Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom
        (IsLocalRing.maximalIdeal _)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackage_eq_comap_or_eq_comap_of_mem_minimalPrimes_natCast_of_specializes.solution
