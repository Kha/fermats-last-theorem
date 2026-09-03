import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import P2M.Util
import P2M.Sol.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit

set_option autoImplicit false

open scoped TensorProduct

universe u₀ u v w w₁ w₂

theorem Algebra.exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R₀ : Type u₀) [CommRing R₀]
    (G : ι → Type v) [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FiniteType R₀ A]
    (B : Type w₂) [CommRing B] [Algebra R₀ B]
    {i : ι} (φ₁ φ₂ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B)
    (h : ∀ x : G i ⊗[R₀] A,
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (φ₁ x) =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (φ₂ x)) :
    ∃ (j : ι) (hij : i ≤ j), ∀ x : G i ⊗[R₀] A,
      Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B) (φ₁ x) =
        Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B) (φ₂ x) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.solution
