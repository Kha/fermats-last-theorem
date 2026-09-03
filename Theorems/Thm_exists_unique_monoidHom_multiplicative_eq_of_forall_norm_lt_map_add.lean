import Mathlib
import P2M.Util
import P2M.Sol.S_exists_unique_monoidHom_multiplicative_eq_of_forall_norm_lt_map_add

set_option autoImplicit false

open Topology

theorem exists_unique_monoidHom_multiplicative_eq_of_forall_norm_lt_map_add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Type*} [Group A]
    {r : ℝ} (hr : 0 < r) (e₀ : V → A)
    (h : ∀ v w : V, ‖v‖ < r → ‖w‖ < r → ‖v + w‖ < r → e₀ (v + w) = e₀ v * e₀ w) :
    ∃! e : Multiplicative V →* A, ∀ v : V, ‖v‖ < r → e (Multiplicative.ofAdd v) = e₀ v := by p2m_exact_reverting @_root_.P2MW.S_exists_unique_monoidHom_multiplicative_eq_of_forall_norm_lt_map_add.solution
