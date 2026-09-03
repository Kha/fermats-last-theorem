import Mathlib
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_map01_oneAddEpsMul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.map01_oneAddEpsMul
    {R : Type u} [CommRing R] {C C' : Scheme.{u}} {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover} {𝒲 : C'.TwoAffineOpenCover}
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))
    (hcomm : fε.hom ≫ (dualNumberThickening A 𝒱 c).hom = (dualNumberThickening A 𝒲 c').hom ≫ f.hom)
    (t : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    fε.map01 (oneAddEpsMul A 𝒱 c t) = oneAddEpsMul A 𝒲 c' (f.map01 t) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_map01_oneAddEpsMul.solution
