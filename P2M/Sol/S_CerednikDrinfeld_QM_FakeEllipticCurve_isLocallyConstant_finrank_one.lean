import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isLocallyConstant_finrank_one

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ] :
    (∀ y : ↥A.A, φ.finrank y =
        φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base (A.f.base y))) ∧
      IsLocallyConstant (fun s : ↥(Spec (CommRingCat.of S)) =>
        φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s)) := by
  have hlc : IsLocallyConstant (Scheme.Hom.finrank φ) := Scheme.Hom.isLocallyConstant_finrank φ
  have hsec : (A.L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ A.f = 𝟙 _ :=
    (A.L.one (𝟙 (Spec (CommRingCat.of S)))).2
  refine ⟨fun y => ?_, ?_⟩
  · have hconn : _root_.IsPreconnected (A.f.base ⁻¹' {A.f.base y}) :=
      (A.bundle.connectedFibres (A.f.base y)).isPreconnected
    have hy : y ∈ A.f.base ⁻¹' {A.f.base y} := rfl
    have hu : (A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base (A.f.base y) ∈ A.f.base ⁻¹' {A.f.base y} := by
      show A.f.base ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base (A.f.base y)) = A.f.base y
      rw [← Scheme.Hom.comp_apply, hsec]
      rfl
    exact hlc.apply_eq_of_isPreconnected hconn hy hu
  · exact hlc.comp_continuous (A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.continuous
