import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
    (R : Type u) [CommRing R] (n : ℕ) (B : Type u) [CommRing B] [Algebra R B]
    (a : Fin (n + 1) → B) (i j : Fin (n + 1)) (hi : IsUnit (a i)) (hj : IsUnit (a j))
    (ψi : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (ψj : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (hψi : ∀ l, ψi (ProjSpace.ratio R n i l) * a i = a l)
    (hψj : ∀ l, ψj (ProjSpace.ratio R n j l) * a j = a l) :
    Spec.map (CommRingCat.ofHom ψi.toRingHom) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
          (ProjSpace.X_mem_one R n i) one_pos =
      Spec.map (CommRingCat.ofHom ψj.toRingHom) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
          (ProjSpace.X_mem_one R n j) one_pos := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq.solution
