import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (B : Type u) [CommRing B] [Algebra A B] :
    ∃ (Z' : Scheme.{u}) (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B))
      (_ : IsClosedImmersion ι') (e : Z' ⟶ Z),
      IsPullback e (ι' ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
      e ≫ ι = ι' ≫ ProjSpace.map A B n := by
  refine ⟨pullback ι (ProjSpace.map A B n), pullback.snd ι (ProjSpace.map A B n), inferInstance,
    pullback.fst ι (ProjSpace.map A B n), ?_, pullback.condition⟩
  exact (IsPullback.of_hasPullback ι (ProjSpace.map A B n)).paste_vert (ProjSpace.isPullback_map A B n)
