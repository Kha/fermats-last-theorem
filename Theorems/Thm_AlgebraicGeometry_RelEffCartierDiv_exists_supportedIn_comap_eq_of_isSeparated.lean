import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_comap_eq_of_isSeparated
    {𝒳 S : Scheme.{u}} {c : 𝒳 ⟶ S} [IsSeparated c] (U : 𝒳.Opens) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv (U.ι ≫ c) r g) :
    ∃ D' : RelEffCartierDiv c r g, D'.SupportedIn U ∧
      D'.I.comap (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) = D.I ∧
      D'.I = D.I.map (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated.solution
