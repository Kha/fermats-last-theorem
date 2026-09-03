import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.isSheaf_functor
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (RelEffCartierDiv.functor f r) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.solution
