import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_Tower_nsmulAlgHom_apply_eq_zero_iff_transition_apply_eq_zero_zmodp
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

open scoped TensorProduct

universe v

theorem PDivisibleGroup.Tower.nsmulAlgHom_apply_eq_zero_iff_transition_apply_eq_zero_zmodp
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (A : ℕ → Type v) [∀ v, CommRing (A v)] [∀ v, HopfAlgebra (ZMod p) (A v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (A v)] [∀ v, Module.Finite (ZMod p) (A v)]
    (t : ∀ v, A (v + 1) →ₐc[ZMod p] A v) (ht : ∀ v, Function.Surjective (t v))
    (hrank : ∀ v, Module.finrank (ZMod p) (A v) = p ^ (v * h))
    (hker : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (A (v + 1)) (p ^ v))
    (v : ℕ) (a : A (v + 1)) :
    PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (A (v + 1)) p a = 0 ↔ t v a = 0 := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_Tower_nsmulAlgHom_apply_eq_zero_iff_transition_apply_eq_zero_zmodp.solution
