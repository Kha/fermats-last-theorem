import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_existsUnique_bialgHom_baseChange_eq_zmodp

open scoped TensorProduct

universe u v w

theorem Bialgebra.existsUnique_bialgHom_baseChange_eq_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [Bialgebra 𝓞 H] [Module.Free 𝓞 H] [Module.Finite 𝓞 H]
    [Algebra.FormallyEtale 𝓞 H]
    (L : Type w) [CommRing L] [Bialgebra 𝓞 L] [Module.Free 𝓞 L] [Module.Finite 𝓞 L]
    (φbar : (ZMod p ⊗[𝓞] H) →ₐc[ZMod p] (ZMod p ⊗[𝓞] L)) :
    ∃! φ : H →ₐc[𝓞] L,
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (φ : H →ₐ[𝓞] L) =
        (φbar : ZMod p ⊗[𝓞] H →ₐ[ZMod p] ZMod p ⊗[𝓞] L) := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_existsUnique_bialgHom_baseChange_eq_zmodp.solution
