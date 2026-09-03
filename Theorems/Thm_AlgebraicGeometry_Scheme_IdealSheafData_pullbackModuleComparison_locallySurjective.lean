import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_pullbackModuleComparison_locallySurjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.pullbackModuleComparison_locallySurjective
    {X X' : Scheme.{u}} (f : X' ⟶ X) (I : X.IdealSheafData) :
    ∀ (U : X'.Opens) (s : Γ((I.comap f).module, U)), ∀ x ∈ U,
      ∃ (V : X'.Opens) (i : V ≤ U), x ∈ V ∧
        ((I.comap f).module).presheaf.map (homOfLE i).op s ∈
          Set.range ((I.pullbackModuleComparison f).app V) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_pullbackModuleComparison_locallySurjective.solution
