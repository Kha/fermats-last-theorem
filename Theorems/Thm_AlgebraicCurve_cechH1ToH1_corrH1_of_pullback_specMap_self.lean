import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_cechH1ToH1_corrH1_of_pullback_specMap_self
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry open AlgebraicCurve hiding placesOf_preimage_eq_preimage_restrictAlong_placesOf open Scheme.TwoAffineOpenCover

theorem AlgebraicCurve.cechH1ToH1_corrH1_of_pullback_specMap_self
    (K : Type u) [Field K] {X : Scheme.{u}} (cX : X ⟶ Spec (.of K))
    [IsIntegral X] [IsSeparated cX] [SmoothOfRelativeDimension 1 cX]
    [IsIntegral (Limits.pullback cX (specMap K K))]
    [IsSeparated (pullback.snd cX (specMap K K))]
    [SmoothOfRelativeDimension 1 (pullback.snd cX (specMap K K))]
    (W : X.TwoAffineOpenCover)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K)) [IsIntegral Y] [IsProper y] [SmoothOfRelativeDimension 1 y]
    (πα πβ : Y ⟶ X) (Hα : πα ≫ cX = y) (Hβ : πβ ≫ cX = y)
    (πα₁ πβ₁ : Y ⟶ Limits.pullback cX (specMap K K))
    (hα₁ : πα₁ ≫ pullback.fst cX (specMap K K) = πα) (hβ₁ : πβ₁ ≫ pullback.fst cX (specMap K K) = πβ)
    (s : (W.cover cX).A01) (z : (W.structureSheafSections cX).H1)
    (hcore : letI X₁ := Limits.pullback cX (specMap K K)
      letI c₁ : X₁ ⟶ Spec (.of K) := pullback.snd cX (specMap K K)
      letI := (AlgebraicCurve.baseToFunctionField c₁).toAlgebra
      letI := (AlgebraicCurve.baseToFunctionField y).toAlgebra
      letI W₁ := W.pullback cX K
      ∀ [Nonempty (W₁.U0 ⊓ W₁.U1 : X₁.Opens)]
        (ψα ψβ : X₁.functionField →ₐ[K] Y.functionField)
        (hψπα : Y.fromSpecStalk (genericPoint Y) ≫ πα₁ =
          Spec.map (CommRingCat.ofHom ψα.toRingHom) ≫ X₁.fromSpecStalk (genericPoint X₁))
        (hψπβ : Y.fromSpecStalk (genericPoint Y) ≫ πβ₁ =
          Spec.map (CommRingCat.ofHom ψβ.toRingHom) ≫ X₁.fromSpecStalk (genericPoint X₁))
        (hψα : ψα.toRingHom.IsIntegral) (hψβ : ψβ.toRingHom.IsIntegral) (htrψα : TraceIntegralAlong ψα hψα)
        (hW₁ : AlgebraicCurve.placesOf c₁ W₁.U0 ∪ AlgebraicCurve.placesOf c₁ W₁.U1 = Set.univ)
        (hs₁ : (X₁.germToFunctionField (W₁.U0 ⊓ W₁.U1)).hom ((HomOver.baseChange W cX K).map01 s) ∈
          AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c₁ W₁.U0 ∩ AlgebraicCurve.placesOf c₁ W₁.U1)
            (0 : AlgebraicCurve.Divisor K X₁.functionField)),
        ∃ (sr₁ : (W₁.cover c₁).A01)
          (hsrr₁ : (X₁.germToFunctionField (W₁.U0 ⊓ W₁.U1)).hom sr₁ ∈
            AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c₁ W₁.U0 ∩ AlgebraicCurve.placesOf c₁ W₁.U1)
              (0 : AlgebraicCurve.Divisor K X₁.functionField))
          (x₁' : AlgebraicCurve.cechH1 ((AlgebraicCurve.Place.restrictAlong ψα hψα) ⁻¹' AlgebraicCurve.placesOf c₁ W₁.U0)
            ((AlgebraicCurve.Place.restrictAlong ψα hψα) ⁻¹' AlgebraicCurve.placesOf c₁ W₁.U1)
            (0 : AlgebraicCurve.Divisor K Y.functionField)),
          Scheme.TwoAffineOpenCover.H1baseChangeMap W cX K z = Submodule.Quotient.mk sr₁ ∧
          AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ ψα hψα hW₁) 0 x₁' =
            AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ ψβ hψβ hW₁) 0
              (AlgebraicCurve.cechH1.pullbackAlong ψβ hψβ _ _
                (Submodule.Quotient.mk ⟨(X₁.germToFunctionField (W₁.U0 ⊓ W₁.U1)).hom
                  ((HomOver.baseChange W cX K).map01 s), hs₁⟩)) ∧
          AlgebraicCurve.cechH1ToH1 hW₁ 0
              (Submodule.Quotient.mk ⟨(X₁.germToFunctionField (W₁.U0 ⊓ W₁.U1)).hom sr₁, hsrr₁⟩) =
            AlgebraicCurve.cechH1ToH1 hW₁ 0 (AlgebraicCurve.cechH1.traceAlong ψα hψα htrψα _ _ x₁')) :
    letI := (AlgebraicCurve.baseToFunctionField cX).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField y).toAlgebra
    ∀ [Nonempty (W.U0 ⊓ W.U1 : X.Opens)]
      (φα φβ : X.functionField →ₐ[K] Y.functionField)
      (hφπα : Y.fromSpecStalk (genericPoint Y) ≫ πα =
        Spec.map (CommRingCat.ofHom φα.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
      (hφπβ : Y.fromSpecStalk (genericPoint Y) ≫ πβ =
        Spec.map (CommRingCat.ofHom φβ.toRingHom) ≫ X.fromSpecStalk (genericPoint X))
      (hφα : φα.toRingHom.IsIntegral) (hφβ : φβ.toRingHom.IsIntegral) (htrα : TraceIntegralAlong φα hφα)
      (hW : AlgebraicCurve.placesOf cX W.U0 ∪ AlgebraicCurve.placesOf cX W.U1 = Set.univ)
      (hsr : (X.germToFunctionField (W.U0 ⊓ W.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf cX W.U0 ∩ AlgebraicCurve.placesOf cX W.U1)
          (0 : AlgebraicCurve.Divisor K X.functionField)),
      ∃ (sr : (W.cover cX).A01)
        (hsrr : (X.germToFunctionField (W.U0 ⊓ W.U1)).hom sr ∈
          AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf cX W.U0 ∩ AlgebraicCurve.placesOf cX W.U1)
            (0 : AlgebraicCurve.Divisor K X.functionField))
        (x' : AlgebraicCurve.cechH1 ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf cX W.U0)
          ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf cX W.U1)
          (0 : AlgebraicCurve.Divisor K Y.functionField)),
        z = Submodule.Quotient.mk sr ∧
        AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φα hφα hW) 0 x' =
          AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φβ hφβ hW) 0
            (AlgebraicCurve.cechH1.pullbackAlong φβ hφβ _ _
              (Submodule.Quotient.mk ⟨(X.germToFunctionField (W.U0 ⊓ W.U1)).hom s, hsr⟩)) ∧
        AlgebraicCurve.cechH1ToH1 hW 0
            (Submodule.Quotient.mk ⟨(X.germToFunctionField (W.U0 ⊓ W.U1)).hom sr, hsrr⟩) =
          AlgebraicCurve.cechH1ToH1 hW 0 (AlgebraicCurve.cechH1.traceAlong φα hφα htrα _ _ x') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_cechH1ToH1_corrH1_of_pullback_specMap_self.solution
