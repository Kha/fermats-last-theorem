import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_of_isIsogenyPair_of_comp_eq_comp_of_isPullbackVia

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isIsogenyPair_of_isIsogenyPair_of_comp_eq_comp_of_isPullbackVia
    {N : ℕ} {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {k₀ : Type} [Field k₀] (A₀ : FakeEllipticCurve Λ N k₀)
    {Bb : Type} [CommRing Bb] (ψb : k₀ →+* Bb)
    (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A) (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA)

    (huniq : ∀ (χ χ' : A₀.A ⟶ A₀.A) (hχ : χ ≫ A₀.f = A₀.f) (hχ' : χ' ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt χ hχ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt χ hχ P) (mapPt χ hχ Q)) →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt χ' hχ' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt χ' hχ' P) (mapPt χ' hχ' Q)) →
      gA ≫ χ = gA ≫ χ' → χ = χ')
    (d : ℕ) (φ ψ : Ab.A ⟶ Ab.A) (hpair : FakeEllipticCurve.IsIsogenyPair d Ab Ab φ ψ)
    (φ₀ ψ₀ : A₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = A₀.f) (hψ₀ : ψ₀ ≫ A₀.f = A₀.f)
    (hφ₀hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt φ₀ hφ₀ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q))
    (hψ₀hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt ψ₀ hψ₀ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt ψ₀ hψ₀ P) (mapPt ψ₀ hψ₀ Q))
    (hφg : φ ≫ gA = gA ≫ φ₀) (hψg : ψ ≫ gA = gA ≫ ψ₀) :
    FakeEllipticCurve.IsIsogenyPair d A₀ A₀ φ₀ ψ₀ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_of_isIsogenyPair_of_comp_eq_comp_of_isPullbackVia.solution
