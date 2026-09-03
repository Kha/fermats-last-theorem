import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import P2M.Util
import P2M.Sol.S_CochainCx_Bounded_exists_kunneth_toModule_HTot_tensor_injective

set_option autoImplicit false

open TensorProduct
open scoped DirectSum

universe u

theorem CochainCx.Bounded.exists_kunneth_toModule_HTot_tensor_injective
    {k : Type u} [Field k] (C D : CochainCx.Bounded k) (n : ℕ) :
    ∃ κ : ∀ i : DoubleComplex.Diag n, (C.H i.1.1 ⊗[k] D.H i.1.2) →ₗ[k] DoubleComplex.HTot (C.tensor D) n,
      (∀ (i : DoubleComplex.Diag n) (x : ↥(LinearMap.ker (C.d i.1.1))) (y : ↥(LinearMap.ker (D.d i.1.2))),
        ∃ hz : (Pi.single i (x.1 ⊗ₜ[k] y.1 : (C.tensor D).C i.1.1 i.1.2) : DoubleComplex.Tot (C.tensor D) n) ∈
            LinearMap.ker (DoubleComplex.dTot (C.tensor D) n),
          κ i (Submodule.Quotient.mk x ⊗ₜ[k] Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨_, hz⟩) ∧
      Function.Injective (DirectSum.toModule k (DoubleComplex.Diag n) (DoubleComplex.HTot (C.tensor D) n) κ) := by p2m_exact_reverting @_root_.P2MW.S_CochainCx_Bounded_exists_kunneth_toModule_HTot_tensor_injective.solution
