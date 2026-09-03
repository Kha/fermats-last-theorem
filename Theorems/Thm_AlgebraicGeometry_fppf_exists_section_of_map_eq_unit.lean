import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit

set_option autoImplicit false

open CategoryTheory Abelian Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.fppf_exists_section_of_map_eq_unit
    {E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}}
    (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)))
    (e : ToType (E.obj.obj (op (Spec (.of ℤ)))))
    (he : g.hom.app (op (Spec (.of ℤ))) e =
      (CategoryTheory.constantSheafAdj Scheme.fppfTopology.{0} AddCommGrpCat.{1}
          AlgebraicGeometry.specZIsTerminal).unit.app (.of (ULift.{1} ℤ)) (ULift.up 1)) :
    ∃ s : (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)) ⟶ E,
      s ≫ g = 𝟙 _ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit.solution
