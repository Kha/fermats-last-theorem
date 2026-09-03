import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_flat_surjective_locallyQuasiFinite_of_locallyQuasiFinite_primePow
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic_of_locallyQuasiFinite_primePow
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard

set_option maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of ℤ))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) c)
    (D : RelativePic0Designation ℤ c) (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hconn : GeometricallyConnected D.toBase)
    (hA : ∀ s : Spec (CommRingCat.of ℤ), s.asIdeal = Ideal.span {(p : ℤ)} → ∀ k : ℕ, 0 < k →
      LocallyQuasiFinite (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).fibre s).schemeNsmul
        (p ^ k)))
    (hB : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ k : ℕ, 0 < k →
      LocallyQuasiFinite (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))))).schemeNsmul (ℓ ^ k))) :
    (∀ n : ℕ, 0 < n →
      Flat ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).schemeNsmul n)) ∧
    (∀ n : ℕ, 0 < n →
      Surjective ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).schemeNsmul n)) ∧
    (∀ n : ℕ, 0 < n →
      LocallyQuasiFinite ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).schemeNsmul n)) := by
  haveI := hsm
  haveI := hconn
  exact GoodReductionJacobian.RelativeGroupLaw.nsmul_flat_surjective_locallyQuasiFinite_of_locallyQuasiFinite_primePow
    p (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD)
    (RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD)
    (fun s => (D.toBase.isConnected_preimage_singleton s).isPreconnected) hA hB
