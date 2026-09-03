import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_connectedComponent_tower_of_isLocalRing_cartierDual
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

universe u v

theorem PDivisibleGroup.exists_connectedComponent_tower_of_isLocalRing_cartierDual
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h : ℕ) (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (hunipL : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v)))) :
    ∃ (h₀ : ℕ) (_ : h₀ ≤ h)
      (R₀ : ℕ → Type v) (_ : ∀ v, CommRing (R₀ v)) (_ : ∀ v, HopfAlgebra 𝓞 (R₀ v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)) (_ : ∀ v, Module.Free 𝓞 (R₀ v))
      (_ : ∀ v, Module.Finite 𝓞 (R₀ v))
      (ρ : ∀ v, L v →ₐc[𝓞] R₀ v) (e : ∀ v, L v) (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v),
    (∀ v, Function.Surjective (t₀ v)) ∧
    (∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀)) ∧
    (∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v)) ∧
    (∀ v, (ρ v).comp (t v) = (t₀ v).comp (ρ (v + 1))) ∧
    ∀ v, IsIdempotentElem (e v) ∧ Coalgebra.counit (R := 𝓞) (e v) = 1 ∧
      Function.Surjective (ρ v) ∧ RingHom.ker (ρ v : L v →ₐ[𝓞] R₀ v) = Ideal.span {1 - e v} ∧
      IsLocalRing (R₀ v) ∧ IsLocalRing (TensorProduct 𝓞 (ZMod p) (R₀ v)) ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (R₀ v))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_connectedComponent_tower_of_isLocalRing_cartierDual.solution
