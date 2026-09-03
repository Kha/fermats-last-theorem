import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_trace_eq_of_isPullback_of_smoothOfRelativeDimension_two_of_mem_maximalIdeal
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.trace_eq_of_isPullback_of_smoothOfRelativeDimension_two_of_mem_maximalIdeal
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {p : ℕ} [Fact p.Prime] (hp : ((p : ℕ) : R) ∈ IsLocalRing.maximalIdeal R)
    (hq : IsUnit ((q : ℕ) : R)) (hq' : IsUnit ((q' : ℕ) : R))
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) [SmoothOfRelativeDimension 2 f]
    {P : Scheme.{u}} {fP : P ⟶ Spec (CommRingCat.of K)} (LP : RelativeGroupLaw K fP)
    (g : P ⟶ 𝒜) (hg : CategoryTheory.IsPullback g fP f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' fP),
      (LP.mul t' x y).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (act : ↥Λ → (P ⟶ P)) (act_over : ∀ x : ↥Λ, act x ≫ fP = fP)
    (act_trace : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : K →+* k)
      (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) fP),
      Function.Injective τ →
      (∀ w : SchemeHomOver (tangentBase k sk) fP, w ∈ Set.range τ ↔ IsTangentVector LP k sk w) →
      (∀ v w : V, τ (v + w) = LP.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
      ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k V Φ = (n : k))
    (act' : ↥Λ → (𝒜 ⟶ 𝒜)) (act'_over : ∀ x : ↥Λ, act' x ≫ f = f)
    (act'_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t f),
      pushPt (act' x) (act'_over x) (L.mul t u v) =
        L.mul t (pushPt (act' x) (act'_over x) u) (pushPt (act' x) (act'_over x) v))
    (act'_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act' ⟨1, h⟩ = 𝟙 𝒜)
    (act'_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act' ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act' y ≫ act' x)
    (act'_add : ∀ (x y : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver t f),
      pushPt (act' (x + y)) (act'_over (x + y)) u =
        L.mul t (pushPt (act' x) (act'_over x) u) (pushPt (act' y) (act'_over y) u))
    (hact : ∀ x : ↥Λ, act x ≫ g = g ≫ act' x) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k)
      (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
      Function.Injective τ →
      (∀ w : SchemeHomOver (tangentBase k sk) f, w ∈ Set.range τ ↔ IsTangentVector L k sk w) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act' m) (act'_over m) (τ v)) →
      ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
        LinearMap.trace k V Φ = (n : k) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_trace_eq_of_isPullback_of_smoothOfRelativeDimension_two_of_mem_maximalIdeal.solution
