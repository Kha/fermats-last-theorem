import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentCharacter_existsUnique_iso_mapIso_eq_of_hasValue_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.existsUnique_iso_mapIso_eq_of_hasValue_one
    {X Y P : Scheme.{u}} {R : Type u} [CommRing R] (f : P ⟶ Spec (CommRingCat.of R))
    (q : X ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (p₁ p₂ : P ⟶ X) (hP : IsPullback p₁ p₂ q q) (T : P ⟶ P) (hT : T ≫ p₁ = p₂)
    (h : T ≫ p₁ ≫ q = p₁ ≫ q) {N M : Y.Modules}
    (hN : Scheme.Modules.IsInvertible N) (hM : Scheme.Modules.IsInvertible M)
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (hβ : HasValue f h
      (((Scheme.Modules.pullbackComp p₁ q).app N).symm ≪≫ (Scheme.Modules.pullback p₁).mapIso β ≪≫
        (Scheme.Modules.pullbackComp p₁ q).app M) 1) :
    ∃! α : N ≅ M, (Scheme.Modules.pullback q).mapIso α = β := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_existsUnique_iso_mapIso_eq_of_hasValue_one.solution
