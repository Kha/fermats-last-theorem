import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : Scheme.Modules.IsLocallyFreeOfRank n E) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback ψ).obj E) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.solution
