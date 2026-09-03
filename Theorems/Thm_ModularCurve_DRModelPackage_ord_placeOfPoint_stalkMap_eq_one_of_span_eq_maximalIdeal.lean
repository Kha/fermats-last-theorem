import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackage_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve
open IsLocalRing

theorem ModularCurve.DRModelPackage.ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (u v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (hmax : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), u, v} = IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x))
    (h𝔭₁ : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), u} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _))
    (h𝔭₂ : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), v} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _))

    (hunr₁ : Ideal.map ((DRModel.baseChangeMap toκ).stalkMap ((𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _)
    (hunr₂ : Ideal.map ((DRModel.baseChangeMap toκ).stalkMap ((𝔛.compZero k).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _) :
    ((𝔛.ratModel k).placeOfPoint ⟨((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n), hy₁⟩).ord
        ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
          (((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n)).hom
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx₁)).hom.hom v)))) = 1 ∧
    ((𝔛.ratModel k).placeOfPoint ⟨((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n), hy₂⟩).ord
        ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
          (((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).stalkMap ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n)).hom
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx₂)).hom.hom u)))) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackage_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal.solution
