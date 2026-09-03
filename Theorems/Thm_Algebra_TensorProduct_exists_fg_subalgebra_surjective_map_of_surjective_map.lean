import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.TensorProduct.exists_fg_subalgebra_surjective_map_of_surjective_map
    {R A D C : Type u} [CommRing R] [CommRing A] [CommRing D] [CommRing C] [Algebra R A] [Algebra R D] [Algebra R C]
    (φ : D →ₐ[R] C) (hφ : φ.toRingHom.FiniteType)
    (hA : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id A A) φ)) (s : Finset A) :
    ∃ (T : Subalgebra R A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.solution
