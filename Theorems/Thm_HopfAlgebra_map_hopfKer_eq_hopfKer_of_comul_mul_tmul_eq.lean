import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul
set_option Elab.async false
set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq
    (K : Type) [Field K] [CharZero K]
    (A : Type) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [Coalgebra.IsCocomm K A]
    (Ā : Type) [CommRing Ā] [HopfAlgebra K Ā] (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (e : A) (he : IsIdempotentElem e)
    (hΔe : Coalgebra.comul (R := K) e * (e ⊗ₜ[K] (1 : A)) = e ⊗ₜ[K] e)
    (hεe : Coalgebra.counit (R := K) e = 1)
    (f : A) (hf : IsIdempotentElem f) (hfK : f ∈ HopfAlgebra.hopfKer π) (hfe : f * e = e)
    (hmin : ∀ b ∈ HopfAlgebra.hopfKer π, b * e = 0 → b * f = 0)
    (Af : Type) [CommRing Af] [HopfAlgebra K Af] (πf : A →ₐc[K] Af) (hπf : Function.Surjective πf)
    (hkerf : RingHom.ker (πf : A →ₐ[K] Af) = Ideal.span {1 - e})
    (Āf : Type) [CommRing Āf] [HopfAlgebra K Āf] (πf' : Ā →ₐc[K] Āf) (hπf' : Function.Surjective πf')
    (hkerf' : RingHom.ker (πf' : Ā →ₐ[K] Āf) = Ideal.span {1 - π e})
    (πff : Af →ₐc[K] Āf) (hcomm : ∀ x : A, πff (πf x) = πf' (π x)) :
    (HopfAlgebra.hopfKer π).map (πf : A →ₐ[K] Af) = HopfAlgebra.hopfKer πff := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq.solution
