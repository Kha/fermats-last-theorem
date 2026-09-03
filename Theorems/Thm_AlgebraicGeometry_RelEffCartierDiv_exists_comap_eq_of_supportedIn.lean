import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_comap_eq_of_supportedIn

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_comap_eq_of_supportedIn
    {𝒳 S : Scheme.{u}} {c : 𝒳 ⟶ S} (U : 𝒳.Opens) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv c r g) (hD : D.SupportedIn U) :
    ∃ D' : RelEffCartierDiv (U.ι ≫ c) r g,
      D'.I = D.I.comap (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_comap_eq_of_supportedIn.solution
