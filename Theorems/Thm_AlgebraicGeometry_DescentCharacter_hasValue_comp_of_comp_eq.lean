import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentCharacter_hasValue_comp_of_comp_eq
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.hasValue_comp_of_comp_eq
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T₁ T₂ : X ⟶ X} {q : X ⟶ Y} (h₁ : T₁ ≫ q = q) (h₂ : T₂ ≫ q = q) (hT₁ : T₁ ≫ f = f)
    (h₁₂ : (T₁ ≫ T₂) ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (c₁ c₂ : R) (hβ₁ : HasValue f h₁ β c₁) (hβ₂ : HasValue f h₂ β c₂) :
    HasValue f h₁₂ β (c₁ * c₂) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_comp_of_comp_eq.solution
