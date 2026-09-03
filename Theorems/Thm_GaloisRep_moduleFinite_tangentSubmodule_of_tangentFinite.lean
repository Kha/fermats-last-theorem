import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_Deformations_TangentSubmodule
import Definitions.Def_Representation_AbsolutelyIrreducible
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_GaloisRep_moduleFinite_tangentSubmodule_of_tangentFinite
attribute [-instance] Deformation.ProartinianCat.instIsResidueAlgebraDualNumberResidueField Deformation.ProartinianCat.instDiscreteTopologyCarrierDualNumbers Deformation.ProartinianCat.instTopologicalSpaceDualNumberResidueField Deformation.ProartinianCat.instDiscreteTopologyDualNumberResidueField Deformation.ProartinianCat.instIsArtinianRingDualNumberResidueField Deformation.ProartinianCat.instFiniteResidueFieldDualNumber Deformation.ProartinianCat.instIsLocalHomDualNumberResidueFieldRingHomAlgebraMap Deformation.ProartinianCat.instIsLocalProartinianAlgebraDualNumberResidueField

set_option autoImplicit false
open CategoryTheory IsLocalRing
theorem GaloisRep.moduleFinite_tangentSubmodule_of_tangentFinite
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    [Representation.IsAbsolutelyIrreducible.{0} (Deformation.matrixRepresentation ρ₀.toMonoidHom)]
    (hfin : GaloisRep.TangentFinite 𝒪 ρbar 𝒟)
    {R : Deformation.ProartinianCat 𝒪}
    (e : (Deformation.conjQuotSubfunctor (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀)).toFunctor.CorepresentableBy R) :
    Module.Finite (IsLocalRing.ResidueField 𝒪) (Deformation.ProartinianCat.tangentSubmodule R) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_moduleFinite_tangentSubmodule_of_tangentFinite.solution
