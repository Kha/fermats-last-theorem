import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

theorem solution
    {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))))
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    Nonempty ((Scheme.Modules.pullback (rigSection c t P)).obj (N.pullbackAlong ⟨t, Category.comp_id t⟩).L ≅
      𝟙_ T.Modules) := by
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k
    ((Scheme.Modules.pullback (rigSection c (𝟙 _) P)).obj N.L) (N.isInvertible.pullback _)
  exact ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c P ⟨t, Category.comp_id t⟩)).app N.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N.L).symm ≪≫
    (Scheme.Modules.pullback t).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso t⟩
