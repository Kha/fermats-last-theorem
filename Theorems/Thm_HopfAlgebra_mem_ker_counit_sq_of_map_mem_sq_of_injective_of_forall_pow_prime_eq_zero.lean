import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

universe u v w

theorem HopfAlgebra.mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (D : Type v) [CommRing D] [HopfAlgebra k D] [Module.Finite k D]
    (hD : ∀ x : D, Coalgebra.counit (R := k) x = 0 → x ^ p = 0)
    (C : Type w) [CommRing C] [Bialgebra k C]
    (ι : C →ₐc[k] D) (hι : Function.Injective ι)
    (c : C) (hc : Coalgebra.counit (R := k) c = 0)
    (h : ι c ∈ RingHom.ker (Bialgebra.counitAlgHom k D) ^ 2) :
    c ∈ RingHom.ker (Bialgebra.counitAlgHom k C) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero.solution
