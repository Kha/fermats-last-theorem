import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import P2M.Util
import P2M.Sol.S_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Module.Grassmannian.exists_isClosedImmersion_toProjSpace_of_represents
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ)
    (Gr : Scheme.{0}) (p : Gr ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
      Module.Grassmannian A (A ⊗[R] M) k ≃
        {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))})
    (hpt : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1)
    (V : (Fin k → M) → Gr.Opens) (hV : ⨆ x, V x = ⊤) (hVaff : ∀ x, IsAffineOpen (V x))
    (hVchart : ∀ (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A]
      (N : Module.Grassmannian A (A ⊗[R] M) k),
      Set.range (pt A N).1.base ⊆ (V x : Set Gr) ↔
        Function.Bijective fun v : Fin k → A =>
          ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)) :
    ∃ (m : ℕ) (ι : Gr ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R m = p := by p2m_exact_reverting @_root_.P2MW.S_Module_Grassmannian_exists_isClosedImmersion_toProjSpace_of_represents.solution
