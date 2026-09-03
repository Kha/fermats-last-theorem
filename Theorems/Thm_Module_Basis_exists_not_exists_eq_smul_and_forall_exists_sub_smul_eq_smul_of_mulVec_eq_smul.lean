import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Basis_exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul

set_option autoImplicit false

theorem Module.Basis.exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul
    {Λ : Type*} [AddCommGroup Λ] {t : ℕ} (b : Module.Basis (Fin t) ℤ Λ)
    {I : Type*} (T : I → Λ →ₗ[ℤ] Λ) (n : I → ℤ)
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p]
    (m : Fin t → κ) (hm : m ≠ 0)
    (heig : ∀ i, ((LinearMap.toMatrix b b (T i)).map (Int.cast : ℤ → κ)).mulVec m = (n i : κ) • m) :
    ∃ v : Λ, (¬ ∃ w : Λ, v = (p : ℤ) • w) ∧ ∀ i, ∃ w : Λ, T i v - n i • v = (p : ℤ) • w := by p2m_exact_reverting @_root_.P2MW.S_Module_Basis_exists_not_exists_eq_smul_and_forall_exists_sub_smul_eq_smul_of_mulVec_eq_smul.solution
