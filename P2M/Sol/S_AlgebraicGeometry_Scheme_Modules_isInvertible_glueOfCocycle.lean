import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle

set_option autoImplicit false

p2m_open "CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry"

universe u

theorem solution
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c : Scheme.Modules.UnitCocycle U) :
    Scheme.Modules.IsInvertible (Scheme.Modules.glueOfCocycle c) := by
  apply AlgebraicGeometry.Scheme.Modules.isInvertible_of_forall_exists_isFrameOn
  intro x
  have hx : x ∈ (⨆ i, U i) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, Scheme.Modules.glueFrame c i, hi, Scheme.Modules.isFrameOn_glueFrame c i⟩
