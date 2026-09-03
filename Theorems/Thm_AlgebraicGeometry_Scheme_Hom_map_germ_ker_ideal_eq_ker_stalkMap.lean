import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_map_germ_ker_ideal_eq_ker_stalkMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.Hom.map_germ_ker_ideal_eq_ker_stalkMap {X Y : Scheme.{u}} (σ : Y ⟶ X) [IsClosedImmersion σ]
    (y : Y) (U : X.affineOpens) (hx : σ.base y ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) (σ.base y) hx).hom (σ.ker.ideal U) = RingHom.ker (σ.stalkMap y).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_map_germ_ker_ideal_eq_ker_stalkMap.solution
