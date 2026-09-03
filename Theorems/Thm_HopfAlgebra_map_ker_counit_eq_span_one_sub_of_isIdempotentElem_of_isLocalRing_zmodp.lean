import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_map_ker_counit_eq_span_one_sub_of_isIdempotentElem_of_isLocalRing_zmodp

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.map_ker_counit_eq_span_one_sub_of_isIdempotentElem_of_isLocalRing_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [HopfAlgebra 𝓞 H] [Module.Finite 𝓞 H] (hred : IsReduced (ZMod p ⊗[𝓞] H))
    (L : Type w) [CommRing L] [HopfAlgebra 𝓞 L] (j : H →ₐc[𝓞] L) (hj : Function.Injective j)
    (f : H) (hf : IsIdempotentElem f) (hεf : Coalgebra.counit (R := 𝓞) f = 1)
    (hloc : IsLocalRing (L ⧸ Ideal.span {1 - j f})) :
    Ideal.map (j : H →ₐ[𝓞] L) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 H)) = Ideal.span {1 - j f} := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_map_ker_counit_eq_span_one_sub_of_isIdempotentElem_of_isLocalRing_zmodp.solution
