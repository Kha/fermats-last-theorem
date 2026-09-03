import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_sub_one_mul_sum_smul_eq_zero_of_corner_decomposition
attribute [-instance] AlgebraicClosure.Rat.isGalois groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false

open scoped BigOperators

theorem ValuationSubring.sub_one_mul_sum_smul_eq_zero_of_corner_decomposition
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : (AlgebraicClosure ℚ)) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {A : Type} [CommRing A] (χ₁ χ₂ c : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) → A)
    (hχ₁ : ∀ g ∈ P.decompositionSubgroup ℚ, ∀ h ∈ P.decompositionSubgroup ℚ, χ₁ (g * h) = χ₁ g * χ₁ h)
    (hχ₂ : ∀ g ∈ P.decompositionSubgroup ℚ, ∀ h ∈ P.decompositionSubgroup ℚ, χ₂ (g * h) = χ₂ g * χ₂ h)
    (hc : ∀ g ∈ P.decompositionSubgroup ℚ, ∀ h ∈ P.decompositionSubgroup ℚ, c (g * h) = χ₁ g * c h + c g * χ₂ h)
    (hχ₁u : ∀ g ∈ P.decompositionSubgroup ℚ, IsUnit (χ₁ g)) (hχ₂u : ∀ g ∈ P.decompositionSubgroup ℚ, IsUnit (χ₂ g))
    (hχ₂I : ∀ τ ∈ P.inertiaSubgroupIn ℚ, χ₂ τ = 1)
    (hdet : ∀ g ∈ P.decompositionSubgroup ℚ, ∀ e : ℕ, g ζ = ζ ^ e → χ₁ g * χ₂ g = e)
    {t : ℕ} (n : Fin t → ℕ) (u β : Fin t → (AlgebraicClosure ℚ)) (a : Fin t → A)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = (p : (AlgebraicClosure ℚ)) ^ (n i) * u i)
    (hdec : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : (AlgebraicClosure ℚ), ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → c τ = ∑ i, (k i) • a i)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ P.decompositionSubgroup ℚ) (e : ℕ) (hσζ : σ ζ = ζ ^ e) :
    (χ₂ σ ^ 2 - 1) * ∑ i, (n i) • a i = 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_sub_one_mul_sum_smul_eq_zero_of_corner_decomposition.solution
