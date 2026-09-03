import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Finite
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_LinearMap_charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero
import P2M.Util
namespace P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_tateModule_quotient

set_option autoImplicit false

open scoped TensorProduct
open Polynomial

namespace CarayolPL2

theorem sub_one_mul_self_eq_zero_of_surjective {K : Type} [CommRing K]
    {W V : Type} [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
    (g : Module.End K W) (f : Module.End K V) (π : W →ₗ[K] V) (hπ : Function.Surjective π)
    (hcomm : ∀ x, π (g x) = f (π x)) (hg : (g - 1) * (g - 1) = 0) :
    (f - 1) * (f - 1) = 0 := by
  have hcomm' : ∀ x, π ((g - 1) x) = (f - 1) (π x) := fun x => by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hcomm]
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := hπ v
  have h := congrArg π (LinearMap.congr_fun hg x)
  rw [Module.End.mul_apply, hcomm', hcomm', LinearMap.zero_apply, map_zero] at h
  rw [Module.End.mul_apply, LinearMap.zero_apply, h]

end CarayolPL2

open CarayolPL2 in
theorem solution
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsLocalRing O] (ρ : GaloisRepAdic O)
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra ℤ_[p] K]
    (π : K ⊗[ℤ_[p]] TateModule p M →ₗ[K] K ⊗[O] ρ.V) (hπ : Function.Surjective π)
    (hπρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : K ⊗[ℤ_[p]] TateModule p M),
      π ((TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K x) =
        (ρ.ρ σ).baseChange K (π x))
    (q : ℕ)
    (hT : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ x : TateModule p M,
        TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
            (TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x - x) =
          TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x - x) :
    ρ.IsUnipotentOnInertiaAt q := by
  intro P hP σ hσ
  set r : Module.End ℤ_[p] (TateModule p M) :=
    TateModule.rep p M (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ with hr

  have h1 : (r - 1) * (r - 1) = 0 := by
    refine LinearMap.ext fun x => ?_
    have hx := hT P hP σ hσ x
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sub_apply,
      Module.End.one_apply, LinearMap.zero_apply, hx, sub_self]

  set g : Module.End K (K ⊗[ℤ_[p]] TateModule p M) := r.baseChange K with hg
  have h2 : (g - 1) * (g - 1) = 0 := by
    have : g - 1 = (r - 1).baseChange K := by
      rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]
    rw [this, ← LinearMap.baseChange_mul, h1, LinearMap.baseChange_zero]

  set f : Module.End K (K ⊗[O] ρ.V) := (ρ.ρ σ).baseChange K with hf
  have h3 : (f - 1) * (f - 1) = 0 :=
    sub_one_mul_self_eq_zero_of_surjective g f π hπ (fun x => hπρ σ x) h2

  have hrank : Module.finrank K (K ⊗[O] ρ.V) = 2 := by
    rw [Module.finrank_baseChange, ρ.finrank_eq]
  have h4 : LinearMap.charpoly f = (X - 1) ^ 2 :=
    LinearMap.charpoly_eq_X_sub_one_sq_of_sub_one_mul_self_eq_zero hrank f h3

  have h5 : (LinearMap.charpoly (ρ.ρ σ)).map (algebraMap O K) = ((X - 1) ^ 2 : O[X]).map
      (algebraMap O K) := by
    rw [← LinearMap.charpoly_baseChange, ← hf, h4, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_one]
  exact Polynomial.map_injective _ (IsFractionRing.injective O K) h5
