import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul

set_option autoImplicit false

theorem AddMonoidHom.exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul
    {G : Type*} [AddCommGroup G] {M : ℕ} (hM : M ≠ 0)
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ G (M : ℤ))
    (f : G →+ G) (u v : ℤ) (huv : (M : ℤ) ∣ u * v - 1)
    (hf : ∀ x : G, (M : ℤ) • x = 0 → f (f x) = u • f x) :
    ∃ C : AddSubgroup G, IsAddCyclic C ∧ Nat.card C = M ∧ ∀ x ∈ C, f x ∈ C := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_exists_isAddCyclic_natCard_eq_forall_apply_mem_of_apply_apply_eq_smul.solution
