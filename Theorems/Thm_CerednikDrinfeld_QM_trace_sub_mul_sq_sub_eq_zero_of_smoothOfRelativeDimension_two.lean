import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_trace_sub_mul_sq_sub_eq_zero_of_smoothOfRelativeDimension_two

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM~finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension"
open QuaternionAlgebra
open scoped Quaternion

theorem CerednikDrinfeld.QM.trace_sub_mul_sq_sub_eq_zero_of_smoothOfRelativeDimension_two
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    [SmoothOfRelativeDimension 2 f]
    (act : ↥Λ → (A ⟶ A)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k)
    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (m : ↥Λ) (Φ : V →ₗ[k] V) (hΦ : ∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v))
    (n ν : ℤ) (hn : (m : ℍ[ℚ, a, b]) + Star.star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]))
    (hν : (m : ℍ[ℚ, a, b]) * Star.star (m : ℍ[ℚ, a, b]) = ((ν : ℚ) : ℍ[ℚ, a, b])) :
    (LinearMap.trace k V Φ - (n : k)) * ((LinearMap.trace k V Φ - (n : k)) ^ 2 - ((n : k) ^ 2 - 4 * (ν : k))) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_trace_sub_mul_sq_sub_eq_zero_of_smoothOfRelativeDimension_two.solution
