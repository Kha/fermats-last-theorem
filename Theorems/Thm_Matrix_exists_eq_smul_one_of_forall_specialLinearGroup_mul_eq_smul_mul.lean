import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul

set_option autoImplicit false

theorem Matrix.exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul
    (q : ℕ) (k : Type) [Field k] (φ : ZMod q →+* k)
    (B : Matrix (Fin 2) (Fin 2) k) (hB : B.det ≠ 0)
    (h : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) (ZMod q), ∃ c : k,
      B * (γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ = c • ((γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ * B)) :
    ∃ a : k, B = a • (1 : Matrix (Fin 2) (Fin 2) k) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul.solution
