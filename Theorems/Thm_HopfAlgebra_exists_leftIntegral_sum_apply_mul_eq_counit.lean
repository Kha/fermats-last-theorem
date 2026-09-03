import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_leftIntegral_sum_apply_mul_eq_counit

universe u v
theorem HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit {R : Type u} [CommRing R] {B : Type v} [CommRing B] [HopfAlgebra R B]
    [Module.Finite R B] [Module.Free R B] :
    ∃ (n : ℕ) (Λ : Fin n → Module.Dual R B) (u : Fin n → B),
      (∀ j (b : B), (TensorProduct.rid R B) ((Λ j).lTensor B (Coalgebra.comul b)) = (Λ j b) • (1 : B))
      ∧ ∀ b : B, ∑ j, Λ j (u j * b) = Coalgebra.counit b := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_leftIntegral_sum_apply_mul_eq_counit.solution
