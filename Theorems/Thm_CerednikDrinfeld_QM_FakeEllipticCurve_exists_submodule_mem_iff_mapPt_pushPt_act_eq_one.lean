import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_mem_iff_mapPt_pushPt_act_eq_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion
open QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_submodule_mem_iff_mapPt_pushPt_act_eq_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N : ℕ}
    {S : Type u} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f)
    (hφmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x)
    (r : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P₀ : SchemeHomOver t E.f)
    (hP₀ : nsmulPt E.L t r P₀ = E.L.one t) :
    ∃ J : Submodule ℤ ℍ[ℚ, a, b],
      (∀ x, x ∈ J ↔ ∃ hx : x ∈ Λ, mapPt φ hφ (pushPt (E.act ⟨x, hx⟩) (E.act_over _) P₀) = E'.L.one t) ∧
      J ≤ Λ ∧ (∀ y ∈ Λ, (r : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_mem_iff_mapPt_pushPt_act_eq_one.solution
