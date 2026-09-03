import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_injective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_injective
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) [Flat φ] [Surjective φ] :
    Function.Injective fun D : RelEffCartierDiv f r g' => D.pullbackAlong φ hφ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_injective.solution
