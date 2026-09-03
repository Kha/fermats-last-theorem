import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit

set_option autoImplicit false

open TensorProduct

universe u v w

theorem Algebra.TensorProduct.isDirectLimit_map_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (R₀ : Type v) [CommRing R₀]
    (G : ι → Type w) [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (B : Type w) [CommRing B] [Algebra R₀ B] :
    ∃ _ : DirectedSystem (fun i => G i ⊗[R₀] B)
        (fun i j h => ⇑(Algebra.TensorProduct.map (f i j h) (AlgHom.id R₀ B))),
      IsDirectLimit (fun i j h => ⇑(Algebra.TensorProduct.map (f i j h) (AlgHom.id R₀ B)))
        (fun i => ⇑(Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B))) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit.solution
