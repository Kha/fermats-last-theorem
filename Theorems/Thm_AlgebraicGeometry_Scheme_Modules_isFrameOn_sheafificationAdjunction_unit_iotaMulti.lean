import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite
theorem AlgebraicGeometry.Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    {X : Scheme.{u}} {n : ℕ} {M : X.Modules} {U : X.Opens} (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U), ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W),
      ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    Scheme.Modules.IsFrameOn (M := Scheme.Modules.det n M)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((Scheme.Modules.presheafExteriorPower X n).obj M.val)).app (op U)
        (show ((Scheme.Modules.presheafExteriorPower X n).obj M.val).obj (op U) from
          exteriorPower.ιMulti Γ(X, U) n e))
      U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti.solution
