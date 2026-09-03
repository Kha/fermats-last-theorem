import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hH0 : letI := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd c x) ⊤
      Function.Bijective (algebraMap k Γ(pullback c x, ⊤)))
    (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
      (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H0 = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap.solution
