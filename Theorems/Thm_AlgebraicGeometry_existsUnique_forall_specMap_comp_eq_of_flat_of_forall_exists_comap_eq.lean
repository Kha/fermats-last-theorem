import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq
    {B : Type u} [CommRing B] {ι : Type u} [Finite ι]
    (B' : ι → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra B (B' i)] [∀ i, Module.Flat B (B' i)]
    (hcov : ∀ 𝔭 : PrimeSpectrum B, ∃ (i : ι) (𝔮 : PrimeSpectrum (B' i)), PrimeSpectrum.comap (algebraMap B (B' i)) 𝔮 = 𝔭)
    {T : Scheme.{u}} (φ' : ∀ i, Spec (CommRingCat.of (B' i)) ⟶ T)
    (h : ∀ i j, Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B' i →+* B' i ⊗[B] B' j)) ≫ φ' i =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B' j →ₐ[B] B' i ⊗[B] B' j).toRingHom) ≫ φ' j) :
    ∃! φ : Spec (CommRingCat.of B) ⟶ T, ∀ i, Spec.map (CommRingCat.ofHom (algebraMap B (B' i))) ≫ φ = φ' i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq.solution
