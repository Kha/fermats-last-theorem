import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply

universe u v

theorem HopfAlgebra.exists_mem_primitives_forall_apply_pow_eq_convPow_apply
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (a : A)
    (ha : ∀ β γ : WithConv (A →ₗ[k] k),
      (β ^ p ^ n * γ ^ p ^ n).ofConv a =
        (β ^ p ^ n).ofConv a * (γ ^ p ^ n).ofConv 1 +
          (β ^ p ^ n).ofConv 1 * (γ ^ p ^ n).ofConv a) :
    ∃ x ∈ primitives k A, ∀ β : WithConv (A →ₗ[k] k),
      (β.ofConv x) ^ p ^ n = (β ^ p ^ n).ofConv a := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply.solution
