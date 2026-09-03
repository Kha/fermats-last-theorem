import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_TwoGluedCurves_exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

theorem AlgebraicGeometry.TwoGluedCurves.exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType c₁]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n) :
    ∃ N₁ : Finset {p : Spec (CommRingCat.of k) ⟶ C₁ // p ≫ c₁ = 𝟙 _},
      N₁.card = n ∧ (∏ p ∈ N₁, p.1.ker) = (pullback.fst i₁.1 i₂.1).ker ∧
      (∀ p ∈ N₁, Set.range (p.1 ≫ i₁.1).base ⊆ Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base) ∧
      Set.range (pullback.fst i₁.1 i₂.1).base ⊆ ⋃ p ∈ N₁, Set.range p.1.base := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_TwoGluedCurves_exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced.solution
