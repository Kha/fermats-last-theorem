import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_Module_Grassmannian_exists_scheme_represents_and_isAffineOpen_chart_cover
import Theorems.Thm_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents
import P2M.Util
namespace P2MW.S_Module_Grassmannian_exists_scheme_represents_and_isClosedImmersion_toProjSpace
attribute [-simp] CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ) :
    ∃ (Gr : Scheme.{0}) (p : Gr ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        Module.Grassmannian A (A ⊗[R] M) k ≃
          {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}),
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : Module.Grassmannian A (A ⊗[R] M) k),
        (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1) ∧
      ∃ (m : ℕ) (ι : Gr ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)),
        IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R m = p := by
  obtain ⟨Gr, p, pt, V, hnat, hV, hVaff, hVchart⟩ :=
    Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover R M k
  exact ⟨Gr, p, pt, hnat,
    Module.Grassmannian.exists_isClosedImmersion_toProjSpace_of_represents R M k Gr p pt hnat V hV hVaff hVchart⟩
