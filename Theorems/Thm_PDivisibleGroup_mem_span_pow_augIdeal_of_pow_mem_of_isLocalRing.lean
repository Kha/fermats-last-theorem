import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_mem_span_pow_augIdeal_of_pow_mem_of_isLocalRing
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

universe v

theorem PDivisibleGroup.mem_span_pow_augIdeal_of_pow_mem_of_isLocalRing
    (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Function.Surjective (s v))
    (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
    (hkerH : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
    (hlocH : ∀ v, IsLocalRing (H v))
    (n w : ℕ) (hnw : n + 1 ≤ w) (a : H w)
    (ha : a ^ p ∈ Ideal.span ((fun a : H w => a ^ p ^ (n + 1)) ''
          (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) : Set (H w)))) :
    a ∈ Ideal.span ((fun a : H w => a ^ p ^ n) ''
          (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) : Set (H w))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_mem_span_pow_augIdeal_of_pow_mem_of_isLocalRing.solution
