import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
universe u
theorem AlgebraicGeometry.Scheme.finite_fppfCohomology_of_shortExact
    (S : Scheme.{u}) {X : ShortComplex (Sheaf (smallFppfTopology S) Ab.{u + 1})}
    (hX : X.ShortExact) (n : ℕ)
    (h₁ : Finite (fppfCohomology S X.X₁ n)) (h₃ : Finite (fppfCohomology S X.X₃ n)) :
    Finite (fppfCohomology S X.X₂ n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_finite_fppfCohomology_of_shortExact.solution
