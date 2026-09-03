import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} {g : ℕ}
    (L : RelativeGroupLaw B f) (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g)
    (hθ : L.IsFormalCoordinates F θ)
    (a : A ⟶ A) (ha : a ≫ f = f)

    (φ : Fin g → MvPowerSeries (Fin g) B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin g → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval n (φ i) s) = pushPt a ha (θ B' s)) :
    ∀ (k : Type) [Field k] (sk : B →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ Φ : V →ₗ[k] V, (∀ v : V, τ (Φ v) = pushPt a ha (τ v)) →
        LinearMap.trace k V Φ = sk (Matrix.trace (MvFormalGroup.linearPart φ)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates.solution
