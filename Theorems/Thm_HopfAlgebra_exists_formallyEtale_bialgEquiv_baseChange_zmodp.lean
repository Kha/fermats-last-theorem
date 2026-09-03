import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_formallyEtale_bialgEquiv_baseChange_zmodp

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_formallyEtale_bialgEquiv_baseChange_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (Hbar : Type v) [CommRing Hbar] [HopfAlgebra (ZMod p) Hbar] [Coalgebra.IsCocomm (ZMod p) Hbar]
    [Module.Finite (ZMod p) Hbar] [IsReduced Hbar] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra 𝓞 H) (_ : Coalgebra.IsCocomm 𝓞 H)
      (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H) (_ : Algebra.FormallyEtale 𝓞 H),
      Module.finrank 𝓞 H = Module.finrank (ZMod p) Hbar ∧
      Nonempty ((ZMod p ⊗[𝓞] H) ≃ₐc[ZMod p] Hbar) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_formallyEtale_bialgEquiv_baseChange_zmodp.solution
