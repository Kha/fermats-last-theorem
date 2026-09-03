import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_groupCohomology_smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2

set_option autoImplicit false
open CategoryTheory groupCohomology
theorem groupCohomology.smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (χ : (Ω ≃ₐ[K] Ω) → ℤ) (hχlc : IsLevelConstant₁ r χ)
    (hχ : ∀ σ τ : Ω ≃ₐ[K] Ω, (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ))
    (Kχ : IntermediateField K Ω) [FiniteDimensional K Kχ] [Normal K Kχ]
    (hKχ : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ Kχ.fixingSubgroup ↔ (p : ℤ) ∣ χ σ)
    (s : Kχ ≃ₐ[K] Kχ) (hs : ∀ g, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    (hsχ : ∀ σ : Ω ≃ₐ[K] Ω, (p : ℤ) ∣ χ σ - (cyclicLog s hs hfin (AlgEquiv.restrictNormalHom Kχ σ) : ℤ))
    (a : Kˣ) (α : Ωˣ) (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (fun g : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) =>
        (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap
          ((χ g.1) • (Kummer.kummerRep K Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
        - unitsInflate₂ Kχ
            (carryFun s hs hfin (A := Rep.ofAlgebraAutOnUnits K Kχ)
              (Additive.ofMul (Units.map (algebraMap K Kχ).toMonoidHom a))) g)
      ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_smul_kummerCocycle_sub_unitsInflate2_carryFun_mem_levelCoboundaries2.solution
