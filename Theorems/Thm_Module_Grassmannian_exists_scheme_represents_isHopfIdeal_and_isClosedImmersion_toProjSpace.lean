import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import P2M.Util
import P2M.Sol.S_Module_Grassmannian_exists_scheme_represents_isHopfIdeal_and_isClosedImmersion_toProjSpace
attribute [-simp] CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Module.Grassmannian.exists_scheme_represents_isHopfIdeal_and_isClosedImmersion_toProjSpace
    (R : Type) [CommRing R] (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A]
    (ι : Type) (σ : ι → (A →ₐ[R] A)) (k : ℕ) :
    ∃ (H : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (B : Type) [CommRing B] [Algebra R B],
        {N : Module.Grassmannian B (B ⊗[R] A) k //
            (∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) ∧
            (Ideal.span (N.toSubmodule : Set (B ⊗[R] A))).IsHopfIdeal' B ∧
            ∀ (i : ι) (x : B ⊗[R] A), x ∈ N.toSubmodule →
              (σ i).toLinearMap.baseChange B x ∈ N.toSubmodule} ≃
          {g : Spec (CommRingCat.of B) ⟶ H // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B))})
      (hmap : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')
          (N : {N : Module.Grassmannian B (B ⊗[R] A) k //
            (∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) ∧
            (Ideal.span (N.toSubmodule : Set (B ⊗[R] A))).IsHopfIdeal' B ∧
            ∀ (i : ι) (x : B ⊗[R] A), x ∈ N.toSubmodule →
              (σ i).toLinearMap.baseChange B x ∈ N.toSubmodule}),
          (∀ (a x : B' ⊗[R] A), x ∈ (Module.Grassmannian.map φ N.1).toSubmodule →
              a * x ∈ (Module.Grassmannian.map φ N.1).toSubmodule) ∧
          (Ideal.span ((Module.Grassmannian.map φ N.1).toSubmodule : Set (B' ⊗[R] A))).IsHopfIdeal' B' ∧
          ∀ (i : ι) (x : B' ⊗[R] A), x ∈ (Module.Grassmannian.map φ N.1).toSubmodule →
            (σ i).toLinearMap.baseChange B' x ∈ (Module.Grassmannian.map φ N.1).toSubmodule),
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')
          (N : {N : Module.Grassmannian B (B ⊗[R] A) k //
            (∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) ∧
            (Ideal.span (N.toSubmodule : Set (B ⊗[R] A))).IsHopfIdeal' B ∧
            ∀ (i : ι) (x : B ⊗[R] A), x ∈ N.toSubmodule →
              (σ i).toLinearMap.baseChange B x ∈ N.toSubmodule}),
        (pt B' ⟨Module.Grassmannian.map φ N.1, hmap B B' φ N⟩).1 =
          Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt B N).1) ∧
      ∃ (m : ℕ) (ιP : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)),
        IsClosedImmersion ιP ∧ ιP ≫ ProjSpace.π R m = p := by p2m_exact_reverting @_root_.P2MW.S_Module_Grassmannian_exists_scheme_represents_isHopfIdeal_and_isClosedImmersion_toProjSpace.solution
