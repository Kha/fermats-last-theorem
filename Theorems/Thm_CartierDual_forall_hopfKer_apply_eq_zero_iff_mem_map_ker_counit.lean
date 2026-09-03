import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import P2M.Util
import P2M.Sol.S_CartierDual_forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

universe u v w

theorem CartierDual.forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
    [Coalgebra.IsCocomm R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    [Coalgebra.IsCocomm R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) (φ : CartierDual R A) :
    (∀ a ∈ HopfAlgebra.hopfKer π, φ a = 0) ↔
      φ ∈ Ideal.map (CartierDual.map π)
        (RingHom.ker (Bialgebra.counitAlgHom R (CartierDual R B))) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit.solution
