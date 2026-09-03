import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul

theorem AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul
    {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) (σ : A →+ A)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    ∃ e' : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n,
      ((e' (0, 1) : Submodule.torsionBy ℤ A n) : A) =
        σ ((e' (1, 0) : Submodule.torsionBy ℤ A n) : A) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul.solution
