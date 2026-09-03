import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentCharacter_hasValue_map_pullback_of_comm_sq
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter~isBaseScalar_pullback_map"

theorem AlgebraicGeometry.DescentCharacter.hasValue_map_pullback_of_comm_sq
    {X Y X' Y' : Scheme.{u}} {R R' : Type u} [CommRing R] [CommRing R']
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {T' : X' ⟶ X'} {q' : X' ⟶ Y'} (h' : T' ≫ q' = q')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (hq : gX ≫ q = q' ≫ gY) (hT : T' ≫ gX = gX ≫ T)
    (hf : gX ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    {N M : Y.Modules} (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (c : R) (hβ : HasValue f h β c) :
    HasValue f' h'
      ((Scheme.Modules.pullbackComp q' gY).app N ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp gX q).app N).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
        (Scheme.Modules.pullbackComp gX q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
        ((Scheme.Modules.pullbackComp q' gY).app M).symm)
      (φ c) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_map_pullback_of_comm_sq.solution
