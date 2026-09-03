import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_formallyEtale_bialgHom_faithfullyFlat_ker_eq_map_ker_counit_zmodp
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_formallyEtale_bialgHom_faithfullyFlat_ker_eq_map_ker_counit_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (L : Type v) [CommRing L] [HopfAlgebra 𝓞 L] [Coalgebra.IsCocomm 𝓞 L]
    [Module.Free 𝓞 L] [Module.Finite 𝓞 L] (N : ℕ) (hrank : Module.finrank 𝓞 L = p ^ N)
    (R₀ : Type v) [CommRing R₀] [HopfAlgebra 𝓞 R₀] [Module.Free 𝓞 R₀] [Module.Finite 𝓞 R₀]
    (ρ : L →ₐc[𝓞] R₀) (e : L) (he : IsIdempotentElem e) (hε : Coalgebra.counit (R := 𝓞) e = 1)
    (hρ : Function.Surjective ρ) (hk : RingHom.ker (ρ : L →ₐ[𝓞] R₀) = Ideal.span {1 - e})
    (hR₀ : IsLocalRing R₀) :
    ∃ (H : Type v) (_ : CommRing H) (_ : HopfAlgebra 𝓞 H) (_ : Coalgebra.IsCocomm 𝓞 H)
      (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H) (_ : Algebra.FormallyEtale 𝓞 H) (j : H →ₐc[𝓞] L),
      RingHom.ker (ρ : L →ₐ[𝓞] R₀) =
        Ideal.map (j : H →ₐ[𝓞] L) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 H)) ∧
      (j : H →ₐ[𝓞] L).toRingHom.FaithfullyFlat ∧
      (j : H →ₐ[𝓞] L).toRingHom.Finite ∧
      Function.Injective j ∧
      Coalgebra.IsCocomm 𝓞 R₀ ∧
      ∃ a : ℕ, Module.finrank 𝓞 R₀ = p ^ a := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_formallyEtale_bialgHom_faithfullyFlat_ker_eq_map_ker_counit_zmodp.solution
