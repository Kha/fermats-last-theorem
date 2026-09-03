import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_unique_section_of_pullbackSection_closedCover
    {X Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsReduced X]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (σ₁ : 𝟙_ Z₁.Modules ⟶ (Scheme.Modules.pullback i₁).obj L) (σ₂ : 𝟙_ Z₂.Modules ⟶ (Scheme.Modules.pullback i₂).obj L)
    (hagree : Scheme.Modules.pullbackSection (pullback.fst i₁ i₂) σ₁ ≫
        ((Scheme.Modules.pullbackComp (pullback.fst i₁ i₂) i₁).app L).hom ≫
          ((Scheme.Modules.pullbackCongr (pullback.condition (f := i₁) (g := i₂))).app L).hom =
      Scheme.Modules.pullbackSection (pullback.snd i₁ i₂) σ₂ ≫
        ((Scheme.Modules.pullbackComp (pullback.snd i₁ i₂) i₂).app L).hom) :
    ∃ σ : 𝟙_ X.Modules ⟶ L, Scheme.Modules.pullbackSection i₁ σ = σ₁ ∧ Scheme.Modules.pullbackSection i₂ σ = σ₂ ∧
      ∀ σ' : 𝟙_ X.Modules ⟶ L, Scheme.Modules.pullbackSection i₁ σ' = σ₁ → Scheme.Modules.pullbackSection i₂ σ' = σ₂ → σ' = σ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover.solution
