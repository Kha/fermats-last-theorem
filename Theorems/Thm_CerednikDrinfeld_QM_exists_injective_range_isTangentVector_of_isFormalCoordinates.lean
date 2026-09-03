import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} {g : ℕ}
    (L : RelativeGroupLaw B f) (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g)
    (hθ : L.IsFormalCoordinates F θ) (k : Type) [Field k] [Algebra B k] :
    ∃ τ : (Fin g → k) → SchemeHomOver (tangentBase k (algebraMap B k)) f,
      (∀ v, (τ v).1 = (θ (DualNumber k) (fun i => TrivSqZeroExt.inr (v i))).1) ∧
      Function.Injective τ ∧
      (∀ P, P ∈ Set.range τ ↔ IsTangentVector L k (algebraMap B k) P) ∧
      (∀ v w, τ (v + w) = L.mul (tangentBase k (algebraMap B k)) (τ v) (τ w)) ∧
      (∀ (c : k) (v : Fin g → k), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.solution
