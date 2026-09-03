import Mathlib
import Definitions.Def_CerednikDrinfeld_QMLatticeAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_of_isGroupPullback

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.LatticeAction.forall_trace_eq_iff_of_isGroupPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R' R'' : Type} [CommRing R'] [CommRing R''] (ψ : R' →+* R'')
    {A' A'' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')} {f'' : A'' ⟶ Spec (CommRingCat.of R'')}
    (L' : RelativeGroupLaw R' f') (L'' : RelativeGroupLaw R'' f'') (h : A'' ⟶ A')
    (hh : IsGroupPullback ψ L' L'' h) (i' : LatticeAction Λ f' L') (i'' : LatticeAction Λ f'' L'')
    (hact : ∀ x : ↥Λ, i''.act x ≫ h = h ≫ i'.act x)
    (k : Type) [Field k] (sk : R'' →+* k) :
    (∀ (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f''),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f'', P ∈ Set.range τ ↔ IsTangentVector L'' k sk P) →
        (∀ v w : V, τ (v + w) = L''.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i''.act x) (i''.act_over x) (τ v)) →
        ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k)) ↔
    (∀ (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
        (τ : V → SchemeHomOver (tangentBase k (sk.comp ψ)) f'),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k (sk.comp ψ)) f', P ∈ Set.range τ ↔ IsTangentVector L' k (sk.comp ψ) P) →
        (∀ v w : V, τ (v + w) = L'.mul (tangentBase k (sk.comp ψ)) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
        ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_of_isGroupPullback.solution
