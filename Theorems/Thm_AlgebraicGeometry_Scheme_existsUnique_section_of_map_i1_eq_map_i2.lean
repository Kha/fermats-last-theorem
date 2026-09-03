import Mathlib
import Definitions.Def_Algebra_DescentCofaces
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_existsUnique_section_of_map_i1_eq_map_i2

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry Algebra.DescentCofaces
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.existsUnique_section_of_map_i1_eq_map_i2
    (E : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1})
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A] [Algebra.FinitePresentation R A]
    (e : ToType (E.obj.obj (op (Spec (.of A)))))
    (he : E.obj.map (Spec.map (i₁ R A)).op e = E.obj.map (Spec.map (i₂ R A)).op e) :
    ∃! e₀ : ToType (E.obj.obj (op (Spec (.of R)))),
      E.obj.map (Spec.map (CommRingCat.ofHom (algebraMap R A))).op e₀ = e := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_existsUnique_section_of_map_i1_eq_map_i2.solution
