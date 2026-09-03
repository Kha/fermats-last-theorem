import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_levelStructure_lev_comp_of_disjoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.levelStructure_lev_comp_of_disjoint
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S)
    {A' : Scheme.{u}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f') (hc' : L'.IsCommutative)
    (act' : ↥Λ → (A' ⟶ A')) (act'_over : ∀ x : ↥Λ, act' x ≫ f' = f')
    (p : E.A ⟶ A') (hp : p ≫ f' = E.f) [IsFinite p]
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt p hp (E.L.mul t P Q) = L'.mul t (mapPt p hp P) (mapPt p hp Q))
    (hequiv : ∀ x : ↥Λ, E.act x ≫ p = p ≫ act' x)
    (hdisj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt p hp P = L'.one t → FactorsThrough E.lev P → P = E.L.one t) :
    IsClosedImmersion (E.lev ≫ p) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f'),
      FactorsThrough (E.lev ≫ p) P → FactorsThrough (E.lev ≫ p) Q →
        FactorsThrough (E.lev ≫ p) (L'.mul t P Q) ∧ FactorsThrough (E.lev ≫ p) (L'.inv t P)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)), FactorsThrough (E.lev ≫ p) (L'.one t)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f'),
      FactorsThrough (E.lev ≫ p) P → nsmulPt L' t N P = L'.one t) ∧
    (∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f'),
      FactorsThrough (E.lev ≫ p) P → FactorsThrough (E.lev ≫ p) (pushPt (act' x) (act'_over x) P)) ∧
    IsFinite ((E.lev ≫ p) ≫ f') ∧ Flat ((E.lev ≫ p) ≫ f') ∧ LocallyOfFinitePresentation ((E.lev ≫ p) ≫ f') ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ((E.lev ≫ p) ≫ f').finrank s = N ^ 2) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), (N : k) ≠ 0 →
      ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) f' // FactorsThrough (E.lev ≫ p) P},
        ∀ x y : ZMod N × ZMod N, (e (x + y) : SchemeHomOver (geomPoint k sk) f') = L'.mul (geomPoint k sk) (e x) (e y)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_levelStructure_lev_comp_of_disjoint.solution
