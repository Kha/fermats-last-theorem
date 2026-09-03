import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_and_app_eq_norm_smul
    {X X' : Scheme.{u}} (π : X' ⟶ X) (d : ℕ) [IsIso (Scheme.Modules.normModuleUnitEval π d)]
    {P : X'.Modules} (ι' : 𝟙_ X'.Modules ⟶ P) (U : X.Opens)
    (e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules), U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ X'.Modules)).presheaf.map (homOfLE hW).op (e i))
    (s : Γ(P, π ⁻¹ᵁ U)) (hs : Scheme.Modules.IsFrameOn s (π ⁻¹ᵁ U))
    (g : Γ(X', π ⁻¹ᵁ U)) (hg : ι'.app (π ⁻¹ᵁ U) (Scheme.Modules.toUnitSection _ 1) = g • s) :
    letI : Algebra Γ(X, U) Γ(X', π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    ∃ Ω : Γ(Scheme.Modules.normModule π d P, U), Scheme.Modules.IsFrameOn Ω U ∧
      (inv (Scheme.Modules.normModuleUnitEval π d) ≫ (Scheme.Modules.normModuleFunctor π d).map ι').app U
          (Scheme.Modules.toUnitSection U 1) = (Algebra.norm Γ(X, U) g) • Ω := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_and_app_eq_norm_smul.solution
