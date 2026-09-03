import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_section_ne_zero_of_dual_section_ne_zero
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_section_ne_zero_of_dual_section_ne_zero
    {Y : Scheme.{u}} [IsIntegral Y] (hunit : ∀ t : Γ(Y, ⊤), t ≠ 0 → IsUnit t)
    (P : Y.Modules) (hP : Scheme.Modules.IsInvertible P)
    (hs : ∃ s : Γ(P, ⊤), s ≠ 0) (hs' : ∃ s' : Γ(Scheme.Modules.dual P, ⊤), s' ≠ 0) :
    Nonempty (P ≅ 𝟙_ Y.Modules) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_section_ne_zero_of_dual_section_ne_zero.solution
