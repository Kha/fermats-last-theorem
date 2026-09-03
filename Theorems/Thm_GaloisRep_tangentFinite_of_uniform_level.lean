import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_tangentFinite_of_uniform_level

open IsLocalRing
theorem GaloisRep.tangentFinite_of_uniform_level (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [Finite (ResidueField 𝒪)] (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (hM : ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧
      letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
        ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
          (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
      letI : Algebra (ResidueField 𝒪) (ResidueField (DualNumber (ResidueField 𝒪))) :=
        ((IsLocalRing.residue (DualNumber (ResidueField 𝒪))).comp
          (algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪)))).toAlgebra
      ∀ ρ : GaloisRepAdic (DualNumber (ResidueField 𝒪)), 𝒟 ρ →
        ρ.residual.IsEquiv (ρbar.baseChange (ResidueField (DualNumber (ResidueField 𝒪)))) →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ M, σ x = x) → ρ.ρ σ = 1) :
    TangentFinite 𝒪 ρbar 𝒟 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_tangentFinite_of_uniform_level.solution
