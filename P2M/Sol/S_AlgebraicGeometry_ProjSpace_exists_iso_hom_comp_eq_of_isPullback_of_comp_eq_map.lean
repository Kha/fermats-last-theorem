import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (Z : Scheme.{0})
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (Z₁ : Scheme.{0}) (ι₁ : Z₁ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (e₁ : Z₁ ⟶ Z)
    (h₁ : IsPullback e₁ (ι₁ ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (h₁' : e₁ ≫ ι = ι₁ ≫ ProjSpace.map A B n)
    (Z₂ : Scheme.{0}) (ι₂ : Z₂ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (e₂ : Z₂ ⟶ Z)
    (h₂ : IsPullback e₂ (ι₂ ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (h₂' : e₂ ≫ ι = ι₂ ≫ ProjSpace.map A B n) :
    ∃ φ : Z₁ ≅ Z₂, φ.hom ≫ ι₂ = ι₁ ∧ φ.hom ≫ e₂ = e₁ := by
  refine ⟨h₁.isoIsPullback _ _ h₂, ?_, by simp⟩
  apply (AlgebraicGeometry.ProjSpace.isPullback_map A B n).hom_ext
  · rw [Category.assoc, ← h₂', ← Category.assoc, IsPullback.isoIsPullback_hom_fst, h₁']
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd]
