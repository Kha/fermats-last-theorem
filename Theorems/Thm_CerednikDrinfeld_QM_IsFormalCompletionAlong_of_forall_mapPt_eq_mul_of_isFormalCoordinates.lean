import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.IsFormalCompletionAlong.of_forall_mapPt_eq_mul_of_isFormalCoordinates
    {B : Type} [CommRing B] {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (L' : RelativeGroupLaw B f') (F' : MvFormalGroup g' B) (hθ' : L'.IsFormalCoordinates F' θ')
    (h₁ h₂ h₃ : A ⟶ A') (hh₁ : h₁ ≫ f' = f) (hh₂ : h₂ ≫ f' = f) (hh₃ : h₃ ≫ f' = f)
    (hmul : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (P : SchemeHomOver (Scheme.specOver (𝒪 := B) B') f),
      mapPt h₃ hh₃ P = L'.mul (Scheme.specOver (𝒪 := B) B') (mapPt h₁ hh₁ P) (mapPt h₂ hh₂ P))
    (φ₁ φ₂ : Fin g' → MvPowerSeries (Fin g) B)
    (hφ₁ : ∀ i, MvPowerSeries.constantCoeff (φ₁ i) = 0) (hφ₂ : ∀ i, MvPowerSeries.constantCoeff (φ₂ i) = 0)
    (H₁ : IsFormalCompletionAlong θ θ' h₁ hh₁ φ₁) (H₂ : IsFormalCompletionAlong θ θ' h₂ hh₂ φ₂) :
    IsFormalCompletionAlong θ θ' h₃ hh₃
      (fun i => MvPowerSeries.subst (Sum.elim φ₁ φ₂) (F'.toPowerSeries i)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates.solution
