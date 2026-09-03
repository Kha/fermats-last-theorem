import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

set_option maxHeartbeats 3200000 in
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)
    (φ ψ : SchemeHomOver D.toBase D.toBase)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase,
      x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by
  haveI : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt ℓ) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ
  haveI : IsNoetherianRing ↥(GaloisRep.ratLocalizedAt ℓ) := inferInstance
  haveI : Smooth D.toBase := hsm
  haveI : IsReduced D.P :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian D.toBase
  exact AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced
    ℓ c ε D hD hsm hpr hgc φ ψ h
