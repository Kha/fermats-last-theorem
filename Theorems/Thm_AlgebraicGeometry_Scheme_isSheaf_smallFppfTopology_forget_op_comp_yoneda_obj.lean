import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

theorem AlgebraicGeometry.Scheme.isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj
    (S : Scheme.{u}) (X : Over S) :
    Presheaf.IsSheaf (smallFppfTopology S) ((Scheme.Fppf.forget S).op ⋙ yoneda.obj X) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_forget_op_comp_yoneda_obj.solution
