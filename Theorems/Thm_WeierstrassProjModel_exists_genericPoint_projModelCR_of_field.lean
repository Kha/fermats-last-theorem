import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_genericPoint_projModelCR_of_field

open AlgebraicGeometry WeierstrassProjModel

universe u

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem WeierstrassProjModel.exists_genericPoint_projModelCR_of_field
    {K : Type u} [Field K] (V : WeierstrassCurve.Projective K) :
    ∃ η : Proj (projModelGradingCR V),
      η.asHomogeneousIdeal = ⊥ ∧
      closure ({η} : Set (Proj (projModelGradingCR V))) = Set.univ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_genericPoint_projModelCR_of_field.solution
