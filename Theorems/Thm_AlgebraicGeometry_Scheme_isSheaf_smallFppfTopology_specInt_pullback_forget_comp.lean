import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_specInt_pullback_forget_comp
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
theorem AlgebraicGeometry.Scheme.isSheaf_smallFppfTopology_specInt_pullback_forget_comp
    {T : Scheme.{0}} (ι : T ⟶ specInt)
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1}) :
    Presheaf.IsSheaf (smallFppfTopology specInt)
      ((Scheme.Fppf.forget specInt ⋙ Over.pullback ι ⋙ Over.forget T).op ⋙ X.obj) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_specInt_pullback_forget_comp.solution
