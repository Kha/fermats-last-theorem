import Mathlib
import Definitions.Def_Deformations_TraceAlgebra
import Definitions.Def_Representation_AbsolutelyIrreducible
import P2M.Util
import P2M.Sol.S_Deformation_TraceAlgebra_descends
attribute [-instance] Deformation.ProartinianCat.ClosedSubalgebra.instNontrivialSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsLinearTopologySubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsTopologicalRingSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace
attribute [-simp] Deformation.ProartinianCat.closedSubalgebraι_apply Deformation.matrixRepresentation_apply

open CategoryTheory IsLocalRing

universe u v
theorem Deformation.TraceAlgebra.descends
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (IsLocalRing.ResidueField 𝓞)]
    {A : Deformation.ProartinianCat 𝓞}
    {ρ₀ : (Deformation.repnFunctor n G 𝓞).obj Deformation.ProartinianCat.residueField}
    [Representation.IsAbsolutelyIrreducible.{u} (Deformation.toRepresentation ρ₀)]
    {ρ' : G →ₜ* GL n A} (hρ' : ρ' ∈ (Deformation.liftFunctor n G 𝓞 ρ₀).obj A) :
    Deformation.TraceAlgebra.Descends ρ' := by p2m_exact_reverting @_root_.P2MW.S_Deformation_TraceAlgebra_descends.solution
