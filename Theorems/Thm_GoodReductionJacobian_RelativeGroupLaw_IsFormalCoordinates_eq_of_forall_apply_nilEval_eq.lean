import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_eq_of_forall_apply_nilEval_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.eq_of_forall_apply_nilEval_eq
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {g : ℕ} (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (ε ε' : MvFormalGroup.End F)
    (h : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin g → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval m (ε.toPowerSeries i) s) =
          θ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s)) :
    ε = ε' := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_eq_of_forall_apply_nilEval_eq.solution
