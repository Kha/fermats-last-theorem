import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (e : ℕ) (m : ProjSpace.twistFam (ι ≫ ProjSpace.π A n) ι)
    (hm : m ∈ (ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).grade (e : ℤ)) (j : Fin (n + 1)) :
    ∃ (k : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous (e + k)),
      ∀ i : Fin (n + 1),
        (((ProjSpace.twistGradedModule ι (ι ≫ ProjSpace.π A n)).xMul j ^ k) m) ((e + k : ℕ) : ℤ) i =
          ProjSpace.restrictFun
            (inf_le_right : (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart ι i ≤ ProjSpace.pullbackChart ι i)
            ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := e + k
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule (e + k) F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ (e + k), (MvPolynomial.mem_homogeneousSubmodule (e + k) _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i (e + k))⟩
                    den_mem := ⟨e + k, rfl⟩ }))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.solution
