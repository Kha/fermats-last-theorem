import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentCharacter_hasValue_symm_of_mul_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.hasValue_symm_of_mul_eq_one
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (c c' : R) (hβ : HasValue f h β c) (hc : c' * c = 1) :
    HasValue f h β.symm c' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_symm_of_mul_eq_one.solution
