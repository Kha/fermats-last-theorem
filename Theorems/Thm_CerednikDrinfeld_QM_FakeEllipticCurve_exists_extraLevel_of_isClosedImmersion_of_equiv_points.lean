import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_isClosedImmersion_of_equiv_points

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM~exists_comp_eq_of_forall_factorsThrough_of_isReduced NeronModelInfra GoodReductionJacobian"

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_of_isClosedImmersion_of_equiv_points
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ}
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0)
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
    (e : ZMod ℓ × ZMod ℓ ≃ ↥S)
    (he : ∀ x y : ZMod ℓ × ZMod ℓ,
      ((e (x + y) : ↥S) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
        E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (hstab : ∀ (m : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f),
      P ∈ S → pushPt (E.act m) (E.act_over m) P ∈ S)
    (hdisj : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      P ∈ S → FactorsThrough E.lev P → P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    ∃ K : E.ExtraLevel ℓ,
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E.f),
        FactorsThrough K.levK P ↔ FactorsThrough i.1 P) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough K.levK P ↔ P ∈ S) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_isClosedImmersion_of_equiv_points.solution
