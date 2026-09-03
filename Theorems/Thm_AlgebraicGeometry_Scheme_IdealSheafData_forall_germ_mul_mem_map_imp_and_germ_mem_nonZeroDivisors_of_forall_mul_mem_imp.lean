import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_forall_germ_mul_mem_map_imp_and_germ_mem_nonZeroDivisors_of_forall_mul_mem_imp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.forall_germ_mul_mem_map_imp_and_germ_mem_nonZeroDivisors_of_forall_mul_mem_imp
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (x : ↥X) (hx : x ∈ (U : X.Opens)) (t : Γ(X, U))
    (hsat : ∀ s : Γ(X, U), t * s ∈ I.ideal U → s ∈ I.ideal U) (ht : t ∈ nonZeroDivisors Γ(X, U)) :
    (∀ r : X.presheaf.stalk x,
        X.presheaf.germ (U : X.Opens) x hx t * r ∈ (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom →
          r ∈ (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom) ∧
      X.presheaf.germ (U : X.Opens) x hx t ∈ nonZeroDivisors (X.presheaf.stalk x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_forall_germ_mul_mem_map_imp_and_germ_mem_nonZeroDivisors_of_forall_mul_mem_imp.solution
