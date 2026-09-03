import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.topologicalKrullDim_le_of_isClosedImmersion
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι] :
    topologicalKrullDim Z ≤ n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.solution
