import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.supportedIn_ofPoint
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) (U : 𝒞.Opens) (hU : ∀ t : T, a t ∈ U) :
    (RelEffCartierDiv.ofPoint f a ha).SupportedIn U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint.solution
