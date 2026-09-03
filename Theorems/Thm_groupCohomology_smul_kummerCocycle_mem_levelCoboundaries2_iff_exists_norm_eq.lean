import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq
attribute [-simp] groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply

set_option autoImplicit false
open CategoryTheory groupCohomology
theorem groupCohomology.smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (χ : (Ω ≃ₐ[K] Ω) → ℤ) (hχlc : IsLevelConstant₁ r χ)
    (hχ : ∀ σ τ : Ω ≃ₐ[K] Ω, (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ))
    (Kχ : IntermediateField K Ω) [FiniteDimensional K Kχ]
    (hKχ : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ Kχ.fixingSubgroup ↔ (p : ℤ) ∣ χ σ)
    (hsurj : ∃ σ : Ω ≃ₐ[K] Ω, ¬ (p : ℤ) ∣ χ σ)
    (a : Kˣ) (α : Ωˣ) (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (fun g : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) =>
        (χ g.1) • (Kummer.kummerRep K Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
      ∈ levelCoboundaries₂ r (Kummer.kummerRep K Ω p)
    ↔ ∃ w : Kχ, Algebra.norm K w = (a : K) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq.solution
