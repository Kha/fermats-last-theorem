import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_existsUnique_linearMap_forall_eq_pushPt

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.existsUnique_linearMap_forall_eq_pushPt
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (k : Type) [Field k] (sk : B →+* k)
    (V : Type) [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (g : A ⟶ A) (hg : g ≫ f = f)
    (hg_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
      pushPt g hg (L.mul t P Q) = L.mul t (pushPt g hg P) (pushPt g hg Q)) :
    ∃! Φ : V →ₗ[k] V, ∀ v : V, τ (Φ v) = pushPt g hg (τ v) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_existsUnique_linearMap_forall_eq_pushPt.solution
