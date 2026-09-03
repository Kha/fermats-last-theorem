import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentCharacter_hasValue_one_of_isBaseScalar
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.hasValue_one_of_isBaseScalar
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (hT : T ≫ f = f) {M : Y.Modules}
    (γ : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj M) (c : R)
    (hγ : IsBaseScalar f γ.hom c) :
    HasValue f h γ 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_one_of_isBaseScalar.solution
