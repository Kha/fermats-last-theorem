import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import P2M.Util
import P2M.Sol.S_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit

set_option autoImplicit false

open scoped TensorProduct

universe u₀ u v w w₁ w₂

theorem Algebra.exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R₀ : Type u₀) [CommRing R₀]
    (G : ι → Type v) [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FinitePresentation R₀ A]
    (B : Type w₂) [CommRing B] [Algebra R₀ B]
    (φ : R ⊗[R₀] A →ₐ[R] R ⊗[R₀] B) :
    ∃ (i : ι) (φ₀ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B),
      ∀ x : G i ⊗[R₀] A,
        φ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ A) x) =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (φ₀ x) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.solution
