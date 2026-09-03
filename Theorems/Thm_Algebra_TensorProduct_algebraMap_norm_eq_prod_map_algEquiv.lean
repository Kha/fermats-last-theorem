import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv
    (F M : Type*) [Field F] [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
    (R : Type*) [CommRing R] [Algebra F R] (z : R ⊗[F] M) :
    algebraMap R (R ⊗[F] M) (Algebra.norm R z) =
      ∏ g : M ≃ₐ[F] M, Algebra.TensorProduct.map (AlgHom.id F R) (g : M →ₐ[F] M) z := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv.solution
