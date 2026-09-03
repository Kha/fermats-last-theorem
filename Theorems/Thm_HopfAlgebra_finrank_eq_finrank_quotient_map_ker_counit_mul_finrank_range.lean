import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

universe u v w

theorem HopfAlgebra.finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range
    (k : Type u) [Field k]
    {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A]
    {B : Type w} [CommRing B] [HopfAlgebra k B] [Module.Finite k B]
    (φ : A →ₐc[k] B) :
    Module.finrank k B =
      Module.finrank k (B ⧸ Ideal.map (φ : A →ₐ[k] B) (RingHom.ker (Bialgebra.counitAlgHom k A))) *
        Module.finrank k ↥(φ : A →ₐ[k] B).range := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range.solution
