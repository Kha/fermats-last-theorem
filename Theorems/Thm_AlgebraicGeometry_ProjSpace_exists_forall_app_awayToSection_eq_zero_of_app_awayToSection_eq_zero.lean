import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_forall_app_awayToSection_eq_zero_of_app_awayToSection_eq_zero

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_forall_app_awayToSection_eq_zero_of_app_awayToSection_eq_zero
    {A : Type} [CommRing A] (n : ℕ) {Z : Scheme.{0}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (i : Fin (n + 1)) (k : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous k)
    (h : ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
          (HomogeneousLocalization.mk
            { deg := k
              num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule k F).mpr hF⟩
              den := ⟨X i ^ k, (MvPolynomial.mem_homogeneousSubmodule k _).mpr (MvPolynomial.isHomogeneous_X_pow i k)⟩
              den_mem := ⟨k, rfl⟩ })) = 0)
    (m : ℕ) :
    ∃ K : ℕ, m ≤ k + K ∧
      ∀ (hG : (X i ^ K * F).IsHomogeneous (k + K)) (j : Fin (n + 1)),
        ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))
            (HomogeneousLocalization.mk
              { deg := k + K
                num := ⟨X i ^ K * F, (MvPolynomial.mem_homogeneousSubmodule (k + K) _).mpr hG⟩
                den := ⟨X j ^ (k + K), (MvPolynomial.mem_homogeneousSubmodule (k + K) _).mpr (MvPolynomial.isHomogeneous_X_pow j (k + K))⟩
                den_mem := ⟨k + K, rfl⟩ })) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_app_awayToSection_eq_zero_of_app_awayToSection_eq_zero.solution
