import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ChowDatum_nonempty

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.ChowDatum.nonempty {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (.of R)) [IsProper π] [IsIntegral V] : Nonempty (ChowDatum π) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ChowDatum_nonempty.solution
