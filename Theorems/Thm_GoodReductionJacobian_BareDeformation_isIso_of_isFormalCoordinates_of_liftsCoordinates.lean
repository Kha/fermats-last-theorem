import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_BareDeformation_isIso_of_isFormalCoordinates_of_liftsCoordinates
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct
theorem GoodReductionJacobian.BareDeformation.isIso_of_isFormalCoordinates_of_liftsCoordinates
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (Ĝ₁ : MvFormalGroup 2 B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2) (hθ₁ : L₁.IsFormalCoordinates Ĝ₁ θ₁)
    (D : BareDeformation f₁ L₁ B)
    (G G' : MvFormalGroup.Deformation Ĝ₁ B) (θ θ' : RelativeGroupLaw.FormalCoordinates D.f 2)
    (hθ : D.L.IsFormalCoordinates G.F θ) (hθ' : D.L.IsFormalCoordinates G'.F θ')
    (hl : D.LiftsCoordinates θ₁ θ) (hl' : D.LiftsCoordinates θ₁ θ') :
    ∃ φ : MvFormalGroup.Hom G.F G'.F,
      (∃ ψ : MvFormalGroup.Hom G'.F G.F, ψ.comp φ = MvFormalGroup.Hom.id G.F ∧ φ.comp ψ = MvFormalGroup.Hom.id G'.F) ∧
      (∀ i : Fin 2, MvPowerSeries.map (algebraMap B B₁) (φ.toPowerSeries i) = MvPowerSeries.X i) ∧
      ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (φ.toPowerSeries i) s) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_BareDeformation_isIso_of_isFormalCoordinates_of_liftsCoordinates.solution
