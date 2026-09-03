import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_SheafOfModules_Monoidal
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_curveChange_ofPoint_comp_lineBundle_iso_and_idealModule_iso_of_isInvertible
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_curveChange_ofPoint_comp_lineBundle_iso_and_idealModule_iso_of_isInvertible
    {R : Type u} [CommRing R] {X C : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of R)) (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated x] [IsSeparated c]
    (i : C ⟶ X) [IsClosedImmersion i] (hi : i ≫ x = c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (d : T ⟶ C) (hd : d ≫ c = t)
    (hC : (RelEffCartierDiv.ofPoint c d hd).I.IsInvertible)
    (hX : (RelEffCartierDiv.ofPoint x (d ≫ i) (by rw [Category.assoc, hi, hd])).I.IsInvertible) :
    Nonempty ((Scheme.Modules.pullback (curveChange i hi t)).obj
        (RelEffCartierDiv.ofPoint x (d ≫ i) (by rw [Category.assoc, hi, hd])).lineBundle ≅
      (RelEffCartierDiv.ofPoint c d hd).lineBundle) ∧
    Nonempty ((Scheme.Modules.pullback (curveChange i hi t)).obj
        (RelEffCartierDiv.ofPoint x (d ≫ i) (by rw [Category.assoc, hi, hd])).idealModule ≅
      (RelEffCartierDiv.ofPoint c d hd).idealModule) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_curveChange_ofPoint_comp_lineBundle_iso_and_idealModule_iso_of_isInvertible.solution
