import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_image_closedSubgroup_of_isFinite
attribute [-simp] CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.sizeOf_spec NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_image_closedSubgroup_of_isFinite
    {k : Type} [Field k] [IsAlgClosed k]
    {A₀ A : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of k)} {f : A ⟶ Spec (CommRingCat.of k)}
    (L₀ : RelativeGroupLaw k f₀) (L : RelativeGroupLaw k f)
    (hA_sep : IsSeparated f) (hA_lft : LocallyOfFiniteType f)
    (p : A₀ ⟶ A) (hp : p ≫ f = f₀)
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f₀),
      mapPt p hp (L₀.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q))
    (hp_finite : IsFinite p) (hp_flat : Flat p) (hp_fp : LocallyOfFinitePresentation p)
    (C : Scheme.{0}) (j : C ⟶ A₀) (hj_closed : IsClosedImmersion j) (hj_finite : IsFinite (j ≫ f₀)) (hC_red : IsReduced C)
    (hC_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough j (L₀.one t))
    (hC_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f₀),
      FactorsThrough j P → FactorsThrough j Q → FactorsThrough j (L₀.mul t P Q) ∧ FactorsThrough j (L₀.inv t P)) :
    ∃ (C' : Scheme.{0}) (j' : C' ⟶ A),
      IsClosedImmersion j' ∧ IsFinite (j' ≫ f) ∧ Flat (j' ≫ f) ∧ LocallyOfFinitePresentation (j' ≫ f) ∧ IsReduced C' ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough j' (L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
        FactorsThrough j' P → FactorsThrough j' Q → FactorsThrough j' (L.mul t P Q) ∧ FactorsThrough j' (L.inv t P)) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
        FactorsThrough j P → FactorsThrough j' (mapPt p hp P)) ∧

      (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) f),
        FactorsThrough j' Q ↔ ∃ P : SchemeHomOver (geomPoint k' sk) f₀, FactorsThrough j P ∧ mapPt p hp P = Q) ∧

      (∀ s : ↥(Spec (CommRingCat.of k)),
        (j' ≫ f).finrank s = Nat.card {Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f // FactorsThrough j' Q}) ∧

      (∀ m : ℕ, (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
          FactorsThrough j P → nsmulPt L t m (mapPt p hp P) = L.one t) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
          FactorsThrough j' Q → nsmulPt L t m Q = L.one t) ∧

      (∀ (e₀ : A₀ ⟶ A₀) (he₀ : e₀ ≫ f₀ = f₀) (e : A ⟶ A) (he : e ≫ f = f), e₀ ≫ p = p ≫ e →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f₀),
          FactorsThrough j P → FactorsThrough j (pushPt e₀ he₀ P)) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
          FactorsThrough j' Q → FactorsThrough j' (pushPt e he Q)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_image_closedSubgroup_of_isFinite.solution
