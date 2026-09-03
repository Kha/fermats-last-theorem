import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableCovering_isOfFinAddOrder_mk_quotient_lap_of_sum_eq_zero_of_forall_exists_src_mem_iff

set_option autoImplicit false

theorem AlgebraicCurve.SemistableCovering.isOfFinAddOrder_mk_quotient_lap_of_sum_eq_zero_of_forall_exists_src_mem_iff
    (n m : ℕ) (src tgt : Fin m → Fin n) (W : Fin m → ℕ) (hW : ∀ e, 0 < W e)
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S)) :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (W e - 1))
    let ends : (Σ e : Fin m, Fin (W e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = W ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (W e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ x : V → ℤ, (∑ v, x v) = 0 →
      IsOfFinAddOrder (QuotientAddGroup.mk x : (V → ℤ) ⧸ AddSubgroup.closure (Set.range lap)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableCovering_isOfFinAddOrder_mk_quotient_lap_of_sum_eq_zero_of_forall_exists_src_mem_iff.solution
