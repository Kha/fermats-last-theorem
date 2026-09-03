import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (L : Type v) [CommRing L] [HopfAlgebra 𝓞 L] [Coalgebra.IsCocomm 𝓞 L]
    [Module.Free 𝓞 L] [Module.Finite 𝓞 L] :
    ∃ (H : Type v) (_ : CommRing H) (_ : HopfAlgebra 𝓞 H) (_ : Coalgebra.IsCocomm 𝓞 H)
      (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H) (_ : Algebra.FormallyEtale 𝓞 H) (j : H →ₐc[𝓞] L),
      Function.Injective j ∧
      IsReduced (ZMod p ⊗[𝓞] H) ∧
      Function.Bijective ((Ideal.Quotient.mkₐ (ZMod p) (nilradical (ZMod p ⊗[𝓞] L))).comp
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (j : H →ₐ[𝓞] L))) ∧
      ∀ e : L, IsIdempotentElem e → e ∈ Set.range j := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp.solution
