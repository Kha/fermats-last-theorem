import Mathlib
import Definitions.Def_CerednikDrinfeld_QMLatticeAction
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_forall_apply_eq_of_smoothOfRelativeDimension
attribute [-instance] AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
attribute [-simp] AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq

set_option autoImplicit false
open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.LatticeAction.forall_trace_eq_iff_forall_apply_eq_of_smoothOfRelativeDimension
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R' : Type} [CommRing R'] {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f')
    (d : ℕ) (hd : 0 < d) [SmoothOfRelativeDimension d f'] (i' : LatticeAction Λ f' L')
    (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k) (t : ↥Λ → R')
    (ht : ∀ (x : ↥Λ) (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
        (τ : V → SchemeHomOver (tangentBase k sk) f'),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f', P ∈ Set.range τ ↔ IsTangentVector L' k sk P) →
        (∀ v w : V, τ (v + w) = L'.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ Φ : V →ₗ[k] V, (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
          LinearMap.trace k V Φ = sk (t x)) :
    (∀ (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f'),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f', P ∈ Set.range τ ↔ IsTangentVector L' k sk P) →
        (∀ v w : V, τ (v + w) = L'.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
        ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k)) ↔
      ∀ (x : ↥Λ) (n : ℤ), (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) → sk (t x) = (n : k) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_LatticeAction_forall_trace_eq_iff_forall_apply_eq_of_smoothOfRelativeDimension.solution
