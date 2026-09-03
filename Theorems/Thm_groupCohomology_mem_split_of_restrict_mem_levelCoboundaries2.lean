import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import P2M.Util
import P2M.Sol.S_groupCohomology_mem_split_of_restrict_mem_levelCoboundaries2

set_option autoImplicit false

open CategoryTheory groupCohomology
theorem groupCohomology.mem_split_of_restrict_mem_levelCoboundaries2
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [Normal K L]
    (c : levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω))
    (hres : (fun g : (Ω ≃ₐ[L] Ω) × (Ω ≃ₐ[L] Ω) =>
        (c.1 : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → (Rep.ofAlgebraAutOnUnits K Ω))
          ((L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g.1,
           (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g.2))
        ∈ levelCoboundaries₂ (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom))
            (Rep.ofAlgebraAutOnUnits L Ω)) :
    continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) c ∈ {x | ∃ (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ)
          (_ : f ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
          (h : unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)),
          x = continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ⟨unitsInflate₂ L f, h⟩} := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_mem_split_of_restrict_mem_levelCoboundaries2.solution
