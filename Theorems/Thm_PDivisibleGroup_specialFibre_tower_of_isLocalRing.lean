import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_specialFibre_tower_of_isLocalRing

open scoped TensorProduct

universe u v

theorem PDivisibleGroup.specialFibre_tower_of_isLocalRing
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h₀ : ℕ) (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, HopfAlgebra 𝓞 (R₀ v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)] [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v) (ht₀ : ∀ v, Function.Surjective (t₀ v))
    (hrank₀ : ∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀))
    (hker₀ : ∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (R₀ v)) :
    (∀ v, Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v))) ∧
    (∀ v, Module.finrank (ZMod p) (ZMod p ⊗[𝓞] R₀ v) = p ^ (v * h₀)) ∧
    (∀ v, RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t₀ v)) =
      PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (ZMod p ⊗[𝓞] R₀ (v + 1)) (p ^ v)) ∧
    (∀ v, IsLocalRing (ZMod p ⊗[𝓞] R₀ v)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_specialFibre_tower_of_isLocalRing.solution
