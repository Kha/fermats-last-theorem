import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree

set_option autoImplicit false

theorem Matrix.exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree
    (N : ℕ) [NeZero N] (hN : Squarefree N)
    (α : Matrix (Fin 2) (Fin 2) (ZMod N) →+* Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N))
    (hfree : ∃ v₀ : Fin 2 → Fin 2 → ZMod N, ∀ w : Fin 2 → Fin 2 → ZMod N,
      ∃! a : Matrix (Fin 2) (Fin 2) (ZMod N), w = α a v₀)
    (W : Submodule (ZMod N) (Fin 2 → Fin 2 → ZMod N))
    (hWstab : ∀ (a : Matrix (Fin 2) (Fin 2) (ZMod N)) (w : Fin 2 → Fin 2 → ZMod N), w ∈ W → α a w ∈ W)
    (hWcard : Nat.card ↥W = N ^ 2) :
    ∃ θ : ↥(Subalgebra.centralizer (ZMod N) (Set.range α)) ≃ₐ[ZMod N] Matrix (Fin 2) (Fin 2) (ZMod N),
      ∀ (β : Module.End (ZMod N) (Fin 2 → Fin 2 → ZMod N))
        (hβ : β ∈ Subalgebra.centralizer (ZMod N) (Set.range α)),
        Submodule.map β W ≤ W ↔ θ ⟨β, hβ⟩ 1 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_algEquiv_centralizer_forall_map_le_iff_apply_one_zero_eq_zero_of_squarefree.solution
