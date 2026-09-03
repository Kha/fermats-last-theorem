import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Tower_eq_of_frobenius_comp_eq_zmodp
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply

set_option autoImplicit false

open scoped TensorProduct

universe v

theorem PDivisibleGroup.Tower.eq_of_frobenius_comp_eq_zmodp
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (A : ℕ → Type v) [∀ v, CommRing (A v)] [∀ v, HopfAlgebra (ZMod p) (A v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (A v)] [∀ v, Module.Finite (ZMod p) (A v)]
    (t : ∀ v, A (v + 1) →ₐc[ZMod p] A v) (ht : ∀ v, Function.Surjective (t v))
    (hrank : ∀ v, Module.finrank (ZMod p) (A v) = p ^ (v * h))
    (hker : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (A (v + 1)) (p ^ v))
    (e e' : ∀ v : ℕ, A v →ₐ[ZMod p] A v)
    (het : ∀ v, (t v : A (v + 1) →ₐ[ZMod p] A v).comp (e (v + 1)) = (e v).comp (t v : A (v + 1) →ₐ[ZMod p] A v))
    (he't : ∀ v, (t v : A (v + 1) →ₐ[ZMod p] A v).comp (e' (v + 1)) = (e' v).comp (t v : A (v + 1) →ₐ[ZMod p] A v))
    (hF : ∀ (v : ℕ) (a : A (v + 1)), (e (v + 1) a) ^ p = (e' (v + 1) a) ^ p) :
    ∀ v : ℕ, e v = e' v := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Tower_eq_of_frobenius_comp_eq_zmodp.solution
