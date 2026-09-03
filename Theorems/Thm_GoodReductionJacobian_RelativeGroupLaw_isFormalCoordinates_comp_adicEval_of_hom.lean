import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isFormalCoordinates_comp_adicEval_of_hom

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
theorem GoodReductionJacobian.RelativeGroupLaw.isFormalCoordinates_comp_adicEval_of_hom
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) {g : ℕ} (F G : MvFormalGroup g B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (Φ : MvFormalGroup.Hom G F) (Ψ : MvFormalGroup.Hom F G)
    (hΨΦ : Ψ.comp Φ = MvFormalGroup.Hom.id G) (hΦΨ : Φ.comp Ψ = MvFormalGroup.Hom.id F) :
    L.IsFormalCoordinates G
        (fun (C : Type) _ _ (s : Fin g → C) =>
          θ C (fun i => MvFormalGroup.adicEval (Ideal.span (Set.range s)) s (Φ.toPowerSeries i))) ∧
      ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin g → C, (∀ i, s i ∈ J) →
          θ C (fun i => MvFormalGroup.adicEval (Ideal.span (Set.range s)) s (Φ.toPowerSeries i)) =
            θ C (fun i => MvFormalGroup.nilEval n (Φ.toPowerSeries i) s) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFormalCoordinates_comp_adicEval_of_hom.solution
