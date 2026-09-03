import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_presentation_comp_eq_iff_of_isPullback_of_ringEquiv

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_presentation_comp_eq_iff_of_isPullback_of_ringEquiv
    {k k' : Type} [Field k] [Field k'] (e : k ≃+* k')
    {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k'))
    (L : RelativeGroupLaw k f) (L' : RelativeGroupLaw k' f')
    (i : X' ⟶ X) (hi : CategoryTheory.IsPullback i f' f (Spec.map (CommRingCat.ofHom e.toRingHom)))
    (himul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ i =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
          ⟨P.1 ≫ i, by rw [Category.assoc, hi.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ i, by rw [Category.assoc, hi.w, ← Category.assoc, Q.2]⟩).1)

    (V : Type) [AddCommGroup V] [Module k V]
    (τ : V → SchemeHomOver (tangentBase k (RingHom.id k)) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k (RingHom.id k)) f, P ∈ Set.range τ ↔ IsTangentVector L k (RingHom.id k) P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k (RingHom.id k)) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :
    letI : Module k' V := Module.compHom V (e.symm : k' ≃+* k).toRingHom
    ∃ τ' : V → SchemeHomOver (tangentBase k' (RingHom.id k')) f',
      Function.Injective τ' ∧
      (∀ P : SchemeHomOver (tangentBase k' (RingHom.id k')) f', P ∈ Set.range τ' ↔ IsTangentVector L' k' (RingHom.id k') P) ∧
      (∀ v w : V, τ' (v + w) = L'.mul (tangentBase k' (RingHom.id k')) (τ' v) (τ' w)) ∧
      (∀ (c : k') (v : V), (τ' (c • v)).1 = tangentScale k' c ≫ (τ' v).1) ∧

      (∀ (φ : X ⟶ X) (hφ : φ ≫ f = f) (φ' : X' ⟶ X') (hφ' : φ' ≫ f' = f'),
        φ' ≫ i = i ≫ φ →
        ∀ v w : V, τ w = pushPt φ hφ (τ v) ↔ τ' w = pushPt φ' hφ' (τ' v)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_presentation_comp_eq_iff_of_isPullback_of_ringEquiv.solution
