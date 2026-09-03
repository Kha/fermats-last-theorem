import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_finite_and_faithfullyFlat_of_isReduced_baseChange_of_injective_zmodp

open scoped TensorProduct

universe u v w

theorem RingHom.finite_and_faithfullyFlat_of_isReduced_baseChange_of_injective_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [Algebra 𝓞 H] [Module.Free 𝓞 H] [Module.Finite 𝓞 H]
    (hred : IsReduced (ZMod p ⊗[𝓞] H))
    (T : Type w) [CommRing T] [Algebra 𝓞 T] [Module.Free 𝓞 T] [Module.Finite 𝓞 T]
    (ι : H →ₐ[𝓞] T) (hι : Function.Injective ι) :
    ι.toRingHom.Finite ∧ ι.toRingHom.FaithfullyFlat := by p2m_exact_reverting @_root_.P2MW.S_RingHom_finite_and_faithfullyFlat_of_isReduced_baseChange_of_injective_zmodp.solution
