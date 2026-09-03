import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import P2M.Util
namespace P2MW.S_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_crossing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳
        (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n ∧
    (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel κ).C) ⤳
        (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n := by
  constructor
  · exact (genericPoint_specializes ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)).map
      (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base.hom.continuous
  · have h : (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n =
        (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n) := by
      change ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ) ≫ DRModel.baseChangeMap toκ).base n =
        ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compZero κ) ≫ DRModel.baseChangeMap toκ).base n
      rw [pullback.condition]
    rw [h]
    exact (genericPoint_specializes ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n)).map
      (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base.hom.continuous
