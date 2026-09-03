import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_comp_eq_and_isPullbackVia_of_comp_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S'']
    (φ : S →+* S') (ψ : S' →+* S'') (χ : S →+* S'') (hχ : ψ.comp φ = χ)
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S') (E'' : FakeEllipticCurve Λ N S'')

    (g' : E'.A ⟶ E.A) (h' : IsPullbackVia φ E E' g')
    (hlev' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' E'.f),
      (∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g') → FactorsThrough E'.lev P)

    (g : E''.A ⟶ E.A) (h : IsPullbackVia χ E E'' g) :
    ∃ g'' : E''.A ⟶ E'.A, g'' ≫ g' = g ∧ g'' ≫ E'.f = E''.f ≫ Spec.map (CommRingCat.ofHom ψ) ∧
      (∀ k : E''.A ⟶ E'.A, k ≫ g' = g → k ≫ E'.f = E''.f ≫ Spec.map (CommRingCat.ofHom ψ) → k = g'') ∧
      IsPullbackVia ψ E' E'' g'' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_comp_eq_and_isPullbackVia_of_comp_eq.solution
