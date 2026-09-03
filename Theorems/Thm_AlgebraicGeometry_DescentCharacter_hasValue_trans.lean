import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentCharacter_hasValue_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.hasValue_trans
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M P : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj P)
    (c c' : R) (hβ : HasValue f h β c) (hβ' : HasValue f h β' c') :
    HasValue f h (β ≪≫ β') (c * c') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_trans.solution
