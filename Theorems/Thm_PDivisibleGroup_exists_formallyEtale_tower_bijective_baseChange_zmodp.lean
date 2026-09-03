import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_formallyEtale_tower_bijective_baseChange_zmodp

open scoped TensorProduct

universe u v w

theorem PDivisibleGroup.exists_formallyEtale_tower_bijective_baseChange_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (E : ℕ → Type v) [∀ v, CommRing (E v)] [∀ v, HopfAlgebra (ZMod p) (E v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (E v)] [∀ v, Module.Finite (ZMod p) (E v)]
    (hred : ∀ v, IsReduced (E v))
    (s : ∀ v, E (v + 1) →ₐc[ZMod p] E v) (hs : ∀ v, Function.Surjective (s v))
    (hkers : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (E (v + 1)) (p ^ v)) :
    ∃ (Et : ℕ → Type u) (_ : ∀ v, CommRing (Et v)) (_ : ∀ v, HopfAlgebra 𝓞 (Et v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (Et v)) (_ : ∀ v, Module.Free 𝓞 (Et v)) (_ : ∀ v, Module.Finite 𝓞 (Et v))
      (_ : ∀ v, Algebra.FormallyEtale 𝓞 (Et v))
      (st : ∀ v, Et (v + 1) →ₐc[𝓞] Et v)
      (θ : ∀ v, ZMod p ⊗[𝓞] Et v →ₐc[ZMod p] E v),
      (∀ v, Function.Bijective (θ v)) ∧
      (∀ v, (θ v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (st v)) =
        (s v).comp (θ (v + 1))) ∧
      (∀ v, Function.Surjective (st v)) ∧
      (∀ v, RingHom.ker (st v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (Et (v + 1)) (p ^ v)) ∧
      (∀ v, Module.finrank 𝓞 (Et v) = Module.finrank (ZMod p) (E v)) ∧
      (∀ (g : Type w) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g] (v : ℕ),
        Function.Bijective fun f : Et v →ₐ[𝓞] g =>
          (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : g)})).comp f) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_formallyEtale_tower_bijective_baseChange_zmodp.solution
