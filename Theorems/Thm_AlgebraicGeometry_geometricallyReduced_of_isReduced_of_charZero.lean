import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_geometricallyReduced_of_isReduced_of_charZero

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~geometricallyReduced_pullback_snd_specMap_of_isReduced_of_charZero"

theorem AlgebraicGeometry.geometricallyReduced_of_isReduced_of_charZero
    (k : Type) [Field k] [CharZero k] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] [IsReduced X] :
    GeometricallyReduced g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_geometricallyReduced_of_isReduced_of_charZero.solution
