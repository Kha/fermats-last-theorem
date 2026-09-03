import Mathlib
import Definitions.Def_Deformations_ConjQuotSubfunctor
import P2M.Util
import P2M.Sol.S_Deformation_isCorepresentable_conjQuotSubfunctor_of_descends
attribute [-instance] Deformation.ProartinianCat.ClosedSubalgebra.instNontrivialSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsLinearTopologySubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsTopologicalRingSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace
attribute [-simp] Deformation.ProartinianCat.closedSubalgebraι_apply CategoryTheory.Functor.corepresentableByOfIsInitial_homEquiv_symm_apply CategoryTheory.Functor.representableByOfIsInitial_homEquiv_symm_apply CategoryTheory.Functor.corepresentableByOfIsInitial_homEquiv_apply CategoryTheory.Functor.representableByOfIsInitial_homEquiv_apply

open CategoryTheory IsLocalRing

universe u v
theorem Deformation.isCorepresentable_conjQuotSubfunctor_of_descends
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G] [TopologicalSpace G]
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (IsLocalRing.ResidueField 𝓞)]
    {F : CategoryTheory.Subfunctor (Deformation.repnFunctor n G 𝓞)}
    (hconj : Deformation.ConjStable n F) (hrefl : Deformation.ReflectedByInjective n F)
    (hwi : ∃ T : F.toFunctor.Elements, ∀ X, Nonempty (T ⟶ X))
    (hdesc : ∀ (A : Deformation.ProartinianCat 𝓞), ∀ ρ' ∈ F.obj A, Deformation.TraceAlgebra.Descends ρ') :
    (Deformation.conjQuotSubfunctor n F).toFunctor.IsCorepresentable := by p2m_exact_reverting @_root_.P2MW.S_Deformation_isCorepresentable_conjQuotSubfunctor_of_descends.solution
