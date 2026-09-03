import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsIsogenyPair_comp

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair.comp
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    {d₁ d₂ : ℕ} {E E' E'' : FakeEllipticCurve Λ N S}
    {f : E.A ⟶ E'.A} {f' : E'.A ⟶ E.A} {g : E'.A ⟶ E''.A} {g' : E''.A ⟶ E'.A}
    (hf : FakeEllipticCurve.IsIsogenyPair d₁ E E' f f') (hg : FakeEllipticCurve.IsIsogenyPair d₂ E' E'' g g') :
    FakeEllipticCurve.IsIsogenyPair (d₁ * d₂) E E'' (f ≫ g) (g' ≫ f') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsIsogenyPair_comp.solution
