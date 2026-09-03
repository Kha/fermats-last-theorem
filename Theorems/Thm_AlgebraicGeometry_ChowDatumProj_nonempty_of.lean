import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ChowDatumProj_nonempty_of

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.ChowDatumProj.nonempty_of {R : Type u} [CommRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (.of R)) : Nonempty (ChowDatum π) → Nonempty (ChowDatumProj π) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.solution
