import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import P2M.Util
import P2M.Sol.S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.finite_projective_ker_baseChange_of_forall_exists_isUnit
    {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    {C0 C1 F : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup F] [Module R F]
    (δ : C0 →ₗ[R] C1) (Θ : F →ₗ[R] C0) (r : ℕ)
    (hloc : ∀ 𝔮 : PrimeSpectrum A, ∃ g : R, algebraMap R A g ∉ 𝔮.asIdeal ∧
      ∀ (A' : Type u) [CommRing A'] [Algebra R A'], IsUnit (algebraMap R A' g) →
        Module.Finite A' (LinearMap.ker (δ.baseChange A')) ∧
        Module.Projective A' (LinearMap.ker (δ.baseChange A')) ∧
        (∀ 𝔮' : PrimeSpectrum A', Module.rankAtStalk (LinearMap.ker (δ.baseChange A')) 𝔮' = r) ∧
        LinearMap.ker (δ.baseChange A') ≤ LinearMap.range (Θ.baseChange A')) :
    Module.Finite A (LinearMap.ker (δ.baseChange A)) ∧
    Module.Projective A (LinearMap.ker (δ.baseChange A)) ∧
    (∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk (LinearMap.ker (δ.baseChange A)) 𝔮 = r) ∧
    LinearMap.ker (δ.baseChange A) ≤ LinearMap.range (Θ.baseChange A) := by p2m_exact_reverting @_root_.P2MW.S_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit.solution
