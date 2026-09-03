import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

universe u v w w'

theorem PDivisibleGroup.finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] (p : ℕ) [Fact p.Prime] (h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (v : ℕ)
    (R₁ : Type w) [CommRing R₁] [HopfAlgebra 𝓞 R₁] [Module.Free 𝓞 R₁] [Module.Finite 𝓞 R₁]
    (ρ₁ : L (v + 1) →ₐc[𝓞] R₁) (e₁ : L (v + 1)) (he₁ : IsIdempotentElem e₁)
    (hε₁ : Coalgebra.counit (R := 𝓞) e₁ = 1) (hρ₁ : Function.Surjective ρ₁)
    (hk₁ : RingHom.ker (ρ₁ : L (v + 1) →ₐ[𝓞] R₁) = Ideal.span {1 - e₁}) (hR₁ : IsLocalRing R₁)
    (R₀ : Type w') [CommRing R₀] [HopfAlgebra 𝓞 R₀] [Module.Free 𝓞 R₀] [Module.Finite 𝓞 R₀]
    (ρ₀ : L v →ₐc[𝓞] R₀) (e₀ : L v) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝓞) e₀ = 1) (hρ₀ : Function.Surjective ρ₀)
    (hk₀ : RingHom.ker (ρ₀ : L v →ₐ[𝓞] R₀) = Ideal.span {1 - e₀}) (hR₀ : IsLocalRing R₀) :
    Module.Free 𝓞 (R₁ ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 R₁ p) ∧
      Module.finrank 𝓞 R₁ =
        Module.finrank 𝓞 (R₁ ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 R₁ p) * Module.finrank 𝓞 R₀ := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub.solution
