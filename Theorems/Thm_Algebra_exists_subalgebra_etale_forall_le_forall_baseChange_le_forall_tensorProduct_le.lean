import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Algebra.exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Module.Finite k A] :
    ∃ P : Subalgebra k A,
      Algebra.Etale k P ∧

      (∀ S : Subalgebra k A, Algebra.Etale k S → S ≤ P) ∧

      (∀ (K : Type u) [Field K] [Algebra k K] (S : Subalgebra K (K ⊗[k] A)),
          Algebra.Etale K S →
            S ≤ (Algebra.TensorProduct.map (AlgHom.id K K) P.val).range) ∧

      (∀ (B : Type v) [CommRing B] [Algebra k B] [Module.Finite k B] (Q : Subalgebra k B),
          Algebra.Etale k Q → (∀ S : Subalgebra k B, Algebra.Etale k S → S ≤ Q) →
          ∀ S : Subalgebra k (A ⊗[k] B), Algebra.Etale k S →
            S ≤ (Algebra.TensorProduct.map P.val Q.val).range) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_subalgebra_etale_forall_le_forall_baseChange_le_forall_tensorProduct_le.solution
