import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallyEtale_exists_baseChange_algEquiv_of_isReduced_zmodp

open scoped TensorProduct

universe u v

theorem Algebra.FormallyEtale.exists_baseChange_algEquiv_of_isReduced_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (Hbar : Type v) [CommRing Hbar] [Algebra (ZMod p) Hbar] [Module.Finite (ZMod p) Hbar] [IsReduced Hbar] :
    ∃ (H : Type u) (_ : CommRing H) (_ : Algebra 𝓞 H) (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H)
      (_ : Algebra.FormallyEtale 𝓞 H),
      Module.finrank 𝓞 H = Module.finrank (ZMod p) Hbar ∧
      Nonempty ((ZMod p ⊗[𝓞] H) ≃ₐ[ZMod p] Hbar) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallyEtale_exists_baseChange_algEquiv_of_isReduced_zmodp.solution
