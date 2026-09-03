import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

theorem AlgebraicGeometry.TwoGluedCurves.nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible
    (k : Type u) [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (W₁ : X.Opens) (hW₁ : (W₁ : Set X) = (Set.range i₂.1.base)ᶜ) (hoi : IsOpenImmersion ((i₁.1 ⁻¹ᵁ W₁).ι ≫ i₁.1))
    (L₀ : X.Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)

    (r : ℕ) (ε₀ : {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hε₀ : Set.range ε₀.1.base ⊆ (Set.range i₂.1.base)ᶜ)
    (hε₀i : ε₀.1.ker.IsInvertible) (ε₁ : {p : Spec (CommRingCat.of k) ⟶ C₁ // p ≫ c₁ = 𝟙 _}) (hε₁ : ε₁.1 ≫ i₁.1 = ε₀.1)
    {e₁ : ℕ} (v : Fin e₁ → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hv : ∀ j, Set.range (v j).1.base ⊆ (Set.range i₂.1.base)ᶜ)
    (hvi : ∀ j, (v j).1.ker.IsInvertible) (v₁ : Fin e₁ → {p : Spec (CommRingCat.of k) ⟶ C₁ // p ≫ c₁ = 𝟙 _}) (hv₁ : ∀ j, (v₁ j).1 ≫ i₁.1 = (v j).1)

    (r' : ℕ) {d : ℕ} (q : Fin d → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hq : ∀ m, Set.range (q m).1.base ⊆ (Set.range i₁.1.base)ᶜ)
    (hqi : ∀ m, (q m).1.ker.IsInvertible)
    {e₂ : ℕ} (v' : Fin e₂ → {p : Spec (CommRingCat.of k) ⟶ X // p ≫ x = 𝟙 _}) (hv' : ∀ j, Set.range (v' j).1.base ⊆ (Set.range i₁.1.base)ᶜ)
    (hv'i : ∀ j, (v' j).1.ker.IsInvertible)

    (hK : ((pullback.fst i₁.1 i₂.1).ker).IsInvertible) :
    Nonempty (
      (Scheme.Modules.pullback i₁.1).obj
          (L₀ ⊗ (((ε₀.1.ker) ^ r * (∏ m, (q m).1.ker) ^ r').invModule ⊗
            ((∏ j, (v j).1.ker) * (∏ j, (v' j).1.ker)).module)) ⊗
        ((pullback.fst i₁.1 i₂.1).ker).module ≅
      (Scheme.Modules.pullback i₁.1).obj L₀ ⊗
        ((∏ _l : Fin r, ε₁.1.ker).invModule ⊗ ((∏ j, (v₁ j).1.ker) * (pullback.fst i₁.1 i₂.1).ker).module)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TwoGluedCurves_nonempty_pullback_chartModule_tensor_module_ker_fst_iso_of_isInvertible.solution
