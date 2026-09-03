import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.of_iso
    {X : Scheme.{u}} {n : ℕ} {M N : X.Modules} (e : M ≅ N) (h : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsLocallyFreeOfRank n N := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso.solution
