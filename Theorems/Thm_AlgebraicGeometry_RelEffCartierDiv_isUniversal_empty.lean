import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_isUniversal_empty

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.isUniversal_empty {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) :
    (RelEffCartierDiv.empty f (𝟙 S)).IsUniversal := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isUniversal_empty.solution
