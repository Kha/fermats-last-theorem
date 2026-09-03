import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_levelPackage_of_isClosedImmersion_of_equiv_points

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM~exists_comp_eq_of_forall_factorsThrough_of_isReduced NeronModelInfra GoodReductionJacobian"

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_levelPackage_of_isClosedImmersion_of_equiv_points
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ}
    (n : ℕ) [NeZero n] (k : Type) [Field k] [IsAlgClosed k] (hnk : (n : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k)
    (B : Scheme.{0}) (g : B ⟶ Spec (CommRingCat.of k)) (LB : RelativeGroupLaw k g) (i : SchemeHomOver g E.f)
    (hred : IsReduced B) (hfin : IsFinite g) (hget : Etale g) (hci : IsClosedImmersion i.1)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) i =
        E.L.mul t (NeronModelInfra.schemeHomOverComp x i) (NeronModelInfra.schemeHomOverComp y i))
    (S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f))
    (eB : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g ≃ ↥S)
    (heB : ∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g,
      ((eB y : ↥S) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) = NeronModelInfra.schemeHomOverComp y i)
    (e : ZMod n × ZMod n ≃ ↥S)
    (he : ∀ x y : ZMod n × ZMod n,
      ((e (x + y) : ↥S) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
        E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (hstab : ∀ (m : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f),
      P ∈ S → pushPt (E.act m) (E.act_over m) P ∈ S) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
      FactorsThrough i.1 P → FactorsThrough i.1 Q → FactorsThrough i.1 (E.L.mul t P Q) ∧ FactorsThrough i.1 (E.L.inv t P)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough i.1 (E.L.one t)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough i.1 P → nsmulPt E.L t n P = E.L.one t) ∧
    (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
      FactorsThrough i.1 P → FactorsThrough i.1 (pushPt (E.act x) (E.act_over x) P)) ∧
    IsFinite (i.1 ≫ E.f) ∧ Flat (i.1 ≫ E.f) ∧ LocallyOfFinitePresentation (i.1 ≫ E.f) ∧
    (∀ s : ↥(Spec (CommRingCat.of k)), (i.1 ≫ E.f).finrank s = n ^ 2) ∧
    (∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), (n : k') ≠ 0 →
      ∃ e' : ZMod n × ZMod n ≃ {P : SchemeHomOver (geomPoint k' sk) E.f // FactorsThrough i.1 P},
        ∀ x y : ZMod n × ZMod n, (e' (x + y) : SchemeHomOver (geomPoint k' sk) E.f) = E.L.mul (geomPoint k' sk) (e' x) (e' y)) ∧
    (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough i.1 P ↔ P ∈ S) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_levelPackage_of_isClosedImmersion_of_equiv_points.solution
