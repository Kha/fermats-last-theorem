import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_finrank_cotangent_chart_eq_of_smoothOfRelativeDimension

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Scheme.TwoAffineOpenCover
theorem AlgebraicGeometry.exists_finrank_cotangent_chart_eq_of_smoothOfRelativeDimension
    {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (U : X.Opens) (hU : IsAffineOpen U)
    (e₁ : Spec (CommRingCat.of K) ⟶ (U : Scheme.{0})) (he₁ : e₁ ≫ U.ι ≫ f = 𝟙 (Spec (CommRingCat.of K))) :
    letI := algebraOfHom f U
    (U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom.comp (algebraMap K Γ(X, U)) = RingHom.id K ∧
    ∃ (Ω : Type) (_ : AddCommGroup Ω) (_ : Module K Ω) (_ : Module.Finite K Ω)
      (π : ↥((RingHom.ker (U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom).restrictScalars K) →ₗ[K] Ω),
      Function.Surjective π ∧
      (∀ x : ↥((RingHom.ker (U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom).restrictScalars K),
        π x = 0 ↔ (x : Γ(X, U)) ∈ (RingHom.ker (U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom) ^ 2) ∧
      Module.finrank K Ω = n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_finrank_cotangent_chart_eq_of_smoothOfRelativeDimension.solution
