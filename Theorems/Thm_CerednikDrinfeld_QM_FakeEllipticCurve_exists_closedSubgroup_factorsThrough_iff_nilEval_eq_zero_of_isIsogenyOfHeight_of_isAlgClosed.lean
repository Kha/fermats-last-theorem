import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_closedSubgroup_factorsThrough_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_closedSubgroup_factorsThrough_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (k : Type) [Field k] [IsAlgClosed k] (hkr : IsNilpotent ((r : ℕ) : k))
    (A : FakeEllipticCurve Λ N k) (XA : FormalODModule r k) (θA : RelativeGroupLaw.FormalCoordinates A.f 2)
    (hA : A.IsFormalModuleVia coord XA θA)
    (Y : FormalODModule r k) (γ : Series k) (h : ℕ) (hγ : FormalODModule.IsIsogenyOfHeight XA Y γ h) :
    ∃ (K : Scheme.{0}) (ι : K ⟶ A.A),
      IsClosedImmersion ι ∧ IsFinite (ι ≫ A.f) ∧ Flat (ι ≫ A.f) ∧ LocallyOfFinitePresentation (ι ≫ A.f) ∧
      (∀ y : ↥(Spec (CommRingCat.of k)), (ι ≫ A.f).finrank y = r ^ h) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough ι (A.L.one t)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t A.f),
        FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (A.L.mul t P Q) ∧ FactorsThrough ι (A.L.inv t P)) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
        FactorsThrough ι P → FactorsThrough ι (pushPt (A.act x) (A.act_over x) P)) ∧

      (∃ c : ℕ, ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t A.f),
        FactorsThrough ι P → nsmulPt A.L t (r ^ c) P = A.L.one t) ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra k B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (FactorsThrough ι (θA B'' s) ↔ ∀ i, MvFormalGroup.nilEval n (γ i) s = 0)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_closedSubgroup_factorsThrough_iff_nilEval_eq_zero_of_isIsogenyOfHeight_of_isAlgClosed.solution
