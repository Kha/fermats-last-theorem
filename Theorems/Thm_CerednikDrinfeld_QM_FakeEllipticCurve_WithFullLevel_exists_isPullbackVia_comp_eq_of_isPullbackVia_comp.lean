import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_comp_eq_of_isPullbackVia_comp

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_comp_eq_of_isPullbackVia_comp
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m ℓ : ℕ}
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] (φ : S →+* S') (ψ : S' →+* S'')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u₁ : FakeEllipticCurve.WithFullLevel Λ N m S')
    (u'' : FakeEllipticCurve.WithFullLevel Λ N m S'')
    (Cu : u.1.ExtraLevel ℓ) (Cu₁ : u₁.1.ExtraLevel ℓ) (Cu'' : u''.1.ExtraLevel ℓ)
    (g₁ : u₁.1.A ⟶ u.1.A) (g : u''.1.A ⟶ u.1.A)
    (h₁ : FakeEllipticCurve.IsPullbackVia φ u.1 u₁.1 g₁) (h₁P : (u₁.2.P).1 ≫ g₁ = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1)
    (h₁L : (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u₁.1.f),
          (∃ P₀ : T₀ ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g₁) → FactorsThrough u₁.1.lev P))
    (h₁C : (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u₁.1.f),
          FactorsThrough Cu₁.levK P ↔ ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g₁))
    (h : FakeEllipticCurve.IsPullbackVia (ψ.comp φ) u.1 u''.1 g) (hP : (u''.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ (u.2.P).1)
    (hC : (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
          FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ g)) :
    ∃ g' : u''.1.A ⟶ u₁.1.A, g' ≫ g₁ = g ∧
      FakeEllipticCurve.IsPullbackVia ψ u₁.1 u''.1 g' ∧ (u''.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom ψ) ≫ (u₁.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of S'')) (P : SchemeHomOver t' u''.1.f),
          FactorsThrough Cu''.levK P → ∃ P₀ : T₀ ⟶ Cu₁.K, P₀ ≫ Cu₁.levK = P.1 ≫ g') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_comp_eq_of_isPullbackVia_comp.solution
