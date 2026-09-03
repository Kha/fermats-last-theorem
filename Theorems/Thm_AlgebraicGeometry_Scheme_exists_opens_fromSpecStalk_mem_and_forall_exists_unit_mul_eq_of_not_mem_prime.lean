import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_opens_fromSpecStalk_mem_and_forall_exists_unit_mul_eq_of_not_mem_prime

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_opens_fromSpecStalk_mem_and_forall_exists_unit_mul_eq_of_not_mem_prime
    {X : Scheme.{u}} [IsIntegral X] (x : X) (P : Ideal (X.presheaf.stalk x)) [P.IsPrime]
    (a b : X.presheaf.stalk x) (ha : a ∉ P) (hb : b ∉ P) :
    ∃ U : X.Opens, (X.fromSpecStalk x).base ⟨P, inferInstance⟩ ∈ U ∧
      ∀ y : X, y ∈ U → ∃ u : (X.presheaf.stalk y)ˣ,
        algebraMap (X.presheaf.stalk y) X.functionField (u : X.presheaf.stalk y) *
            algebraMap (X.presheaf.stalk x) X.functionField b =
          algebraMap (X.presheaf.stalk x) X.functionField a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_opens_fromSpecStalk_mem_and_forall_exists_unit_mul_eq_of_not_mem_prime.solution
