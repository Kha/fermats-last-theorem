import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesWedge
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact
    {X : Scheme.{u}} {n : ℕ} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : Scheme.Modules.IsLocallyFreeOfRank n S.X₁) (h₃ : Scheme.Modules.IsInvertible S.X₃) :
    Epi (((Scheme.Modules.exteriorPower X n).map S.f ▷ S.X₂) ≫ Scheme.Modules.wedgeVec n S.X₂) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact.solution
