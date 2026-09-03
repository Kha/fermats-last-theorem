import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_comap_eq_top_and_nonempty_module_iso_and_nonempty_invModule_iso_of_disjoint_range_support
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

namespace TopOffSupport

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite"

theorem subsingleton_sections_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (U : Z.Opens) :
    Subsingleton Γ(Z, U) := by
  have hU : U = ⊥ := by ext x; exact isEmptyElim x
  subst hU
  exact CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEmpty)

theorem nonempty_module_top_iso (X : Scheme.{u}) :
    Nonempty ((⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules) := by

  set ι := (⊤ : X.IdealSheafData).subschemeι with hι
  have h0 : ι.unitToPushforwardUnit = 0 := by
    ext U x

    have hs : Subsingleton ↑(((SheafOfModules.pushforward ι.toRingCatSheafHom).obj
        (SheafOfModules.unit ((⊤ : X.IdealSheafData).subscheme).ringCatSheaf)).val.obj U) := by
      change Subsingleton Γ((⊤ : X.IdealSheafData).subscheme, ι ⁻¹ᵁ U.unop)
      exact subsingleton_sections_of_isEmpty _
    exact Subsingleton.elim _ _
  refine ⟨?_⟩
  change kernel ι.unitToPushforwardUnit ≅ _
  exact kernelIsoOfEq h0 ≪≫ kernelZeroIsoSource

theorem main {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    (h : Disjoint (Set.range f.base) (I.support : Set Y)) :
    I.comap f = ⊤ ∧ Nonempty ((I.comap f).module ≅ 𝟙_ X.Modules) ∧ Nonempty ((I.comap f).invModule ≅ 𝟙_ X.Modules) := by

  have htop : I.comap f = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
    ext x
    simp only [Closeds.coe_preimage, Set.mem_preimage, Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact Set.disjoint_left.mp h ⟨x, rfl⟩ hx
  refine ⟨htop, ?_, ?_⟩
  · rw [htop]; exact nonempty_module_top_iso X
  · rw [htop]
    obtain ⟨e⟩ := nonempty_module_top_iso X
    obtain ⟨-, ⟨e'⟩⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_module_tensor_invModule_iso
      (Scheme.IdealSheafData.isInvertible_top (X := X))

    exact ⟨(λ_ _).symm ≪≫ (e.symm ⊗ᵢ Iso.refl _) ≪≫ (β_ _ _) ≪≫ e'⟩

end TopOffSupport

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry in
theorem solution
    {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    (h : Disjoint (Set.range f.base) (I.support : Set Y)) :
    I.comap f = ⊤ ∧ Nonempty ((I.comap f).module ≅ 𝟙_ X.Modules) ∧ Nonempty ((I.comap f).invModule ≅ 𝟙_ X.Modules) :=
  TopOffSupport.main I f h
