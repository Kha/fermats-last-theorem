import Definitions.Def_CerednikDrinfeld_QMModuli
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_act_trace_of_etale

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion
open CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.act_trace_of_etale
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S)
    {P : Scheme.{u}} (g : P ⟶ Spec (CommRingCat.of S)) (LP : RelativeGroupLaw S g)
    (p : E.A ⟶ P) (hg : p ≫ g = E.f) [Etale p]
    (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t E.f),
      mapPt p hg (E.L.mul t x y) = LP.mul t (mapPt p hg x) (mapPt p hg y))
    (act' : ↥Λ → (P ⟶ P)) (act'_over : ∀ x : ↥Λ, act' x ≫ g = g)
    (hequiv : ∀ x : ↥Λ, E.act x ≫ p = p ≫ act' x) :
    ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (sk : S →+* k')
      (V : Type u) [AddCommGroup V] [Module k' V] [Module.Finite k' V] (τ : V → SchemeHomOver (tangentBase k' sk) g),
      Function.Injective τ →
      (∀ Q : SchemeHomOver (tangentBase k' sk) g, Q ∈ Set.range τ ↔ IsTangentVector LP k' sk Q) →
      (∀ v w : V, τ (v + w) = LP.mul (tangentBase k' sk) (τ v) (τ w)) →
      (∀ (c : k') (v : V), (τ (c • v)).1 = tangentScale k' c ≫ (τ v).1) →
      ∀ (m : ↥Λ) (Φ : V →ₗ[k'] V), (∀ v : V, τ (Φ v) = pushPt (act' m) (act'_over m) (τ v)) →
      ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k' V Φ = (n : k') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_act_trace_of_etale.solution
