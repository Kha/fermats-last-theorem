import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_connectedComponent_of_isLocalRing_cartierDual_zmodp
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply

universe u v

theorem HopfAlgebra.exists_connectedComponent_of_isLocalRing_cartierDual_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [HopfAlgebra 𝓞 H] [Coalgebra.IsCocomm 𝓞 H]
    [Module.Free 𝓞 H] [Module.Finite 𝓞 H]
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) H))) :
    ∃ (R₀ : Type v) (_ : CommRing R₀) (_ : HopfAlgebra 𝓞 R₀) (_ : Module.Free 𝓞 R₀)
      (_ : Module.Finite 𝓞 R₀) (ρ : H →ₐc[𝓞] R₀) (e : H),
      IsIdempotentElem e ∧ Coalgebra.counit (R := 𝓞) e = 1 ∧
      Function.Surjective ρ ∧ RingHom.ker (ρ : H →ₐ[𝓞] R₀) = Ideal.span {1 - e} ∧
      IsLocalRing R₀ ∧ IsLocalRing (TensorProduct 𝓞 (ZMod p) R₀) ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R₀)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_connectedComponent_of_isLocalRing_cartierDual_zmodp.solution
