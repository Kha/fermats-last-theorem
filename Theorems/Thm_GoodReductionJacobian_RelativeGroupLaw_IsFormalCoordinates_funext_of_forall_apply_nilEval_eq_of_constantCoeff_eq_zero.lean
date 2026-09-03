import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {g : ℕ} (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (I : Ideal B) (σ σ' : Fin g → MvPowerSeries (Fin g) (B ⧸ I))
    (hσ : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσ' : ∀ i, MvPowerSeries.constantCoeff (σ' i) = 0)
    (h : ∀ (B' : Type) [CommRing B'] [Algebra (B ⧸ I) B'] [Algebra B B'],
      algebraMap B B' = (algebraMap (B ⧸ I) B').comp (Ideal.Quotient.mk I) →
      ∀ (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin g → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval m (σ i) s) = θ B' (fun i => MvFormalGroup.nilEval m (σ' i) s)) :
    σ = σ' := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_funext_of_forall_apply_nilEval_eq_of_constantCoeff_eq_zero.solution
