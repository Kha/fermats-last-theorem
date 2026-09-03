import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_exists_addOrderOf_apply_eq_forall_apply_mem_zmultiples_of_ker_eq_zmultiples

theorem AddMonoidHom.exists_addOrderOf_apply_eq_forall_apply_mem_zmultiples_of_ker_eq_zmultiples
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] {N : ℕ} [NeZero N]
    (e : ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ A N)
    (Q : A) (hQ : addOrderOf Q = N) (φ : A →+ B) (hφ : φ.ker = AddSubgroup.zmultiples Q) :
    ∃ R : A, N • R = 0 ∧ addOrderOf (φ R) = N ∧
      ∀ P : A, N • P = 0 → φ P ∈ AddSubgroup.zmultiples (φ R) := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_exists_addOrderOf_apply_eq_forall_apply_mem_zmultiples_of_ker_eq_zmultiples.solution
