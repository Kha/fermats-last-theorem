import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Etale_isDomain_and_isIntegrallyClosed_stalk

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Etale.isDomain_and_isIntegrallyClosed_stalk {U S : Scheme.{u}} (f : U ⟶ S) [Etale f]
    [IsAffine S] [IsDomain Γ(S, ⊤)] [IsIntegrallyClosed Γ(S, ⊤)] (y : U) :
    IsDomain (U.presheaf.stalk y) ∧ IsIntegrallyClosed (U.presheaf.stalk y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Etale_isDomain_and_isIntegrallyClosed_stalk.solution
