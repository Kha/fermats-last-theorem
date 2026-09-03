import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finrank_quotient_span_pow_mul_finrank_cartierDual_quotient_eq
attribute [-instance] CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

universe u v

theorem HopfAlgebra.finrank_quotient_span_pow_mul_finrank_cartierDual_quotient_eq
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : Type v) [CommRing H] [HopfAlgebra k H] [Module.Finite k H] [Coalgebra.IsCocomm k H] :
    Module.finrank k (H ⧸ Ideal.span ((fun a : H => a ^ p) ''
        (RingHom.ker (Bialgebra.counitAlgHom k H) : Set H))) *
      Module.finrank k (CartierDual k H ⧸ Ideal.span {φ : CartierDual k H | φ 1 = 0 ∧
        ∀ x ∈ Ideal.span ((fun a : H => a ^ p) '' (RingHom.ker (Bialgebra.counitAlgHom k H) : Set H)),
          φ x = 0}) =
      Module.finrank k H := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finrank_quotient_span_pow_mul_finrank_cartierDual_quotient_eq.solution
