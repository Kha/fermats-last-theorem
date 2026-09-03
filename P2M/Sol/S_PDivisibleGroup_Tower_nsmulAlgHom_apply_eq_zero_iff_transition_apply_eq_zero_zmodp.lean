import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
import P2M.Util
namespace P2MW.S_PDivisibleGroup_Tower_nsmulAlgHom_apply_eq_zero_iff_transition_apply_eq_zero_zmodp
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v

theorem solution
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (A : ℕ → Type v) [∀ v, CommRing (A v)] [∀ v, HopfAlgebra (ZMod p) (A v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (A v)] [∀ v, Module.Finite (ZMod p) (A v)]
    (t : ∀ v, A (v + 1) →ₐc[ZMod p] A v) (ht : ∀ v, Function.Surjective (t v))
    (hrank : ∀ v, Module.finrank (ZMod p) (A v) = p ^ (v * h))
    (hker : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (A (v + 1)) (p ^ v))
    (v : ℕ) (a : A (v + 1)) :
    PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (A (v + 1)) p a = 0 ↔ t v a = 0 := by
  haveI : ∀ w, Module.Free (ZMod p) (A w) := fun w => inferInstance
  obtain ⟨⟨e, he⟩, -⟩ :=
    PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
      (ZMod p) p h A t ht hrank hker v
  constructor
  · intro h0
    have h1 : ((e (t v a) : ↥(PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (A (v + 1)) p).range) : A (v + 1)) = 0 := by
      rw [he, h0]
    have h2 : e (t v a) = 0 := Subtype.ext h1
    exact e.injective (h2.trans (map_zero e).symm)
  · intro h0
    rw [← he, h0, map_zero]
    rfl
