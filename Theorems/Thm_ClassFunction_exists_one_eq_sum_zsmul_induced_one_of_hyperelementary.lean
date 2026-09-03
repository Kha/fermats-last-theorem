import Mathlib
import Definitions.Def_ClassFunction_Induced
import P2M.Util
import P2M.Sol.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary

set_option autoImplicit false

theorem ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
    {G : Type} [Group G] [Fintype G] :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (a : Fin k → ℤ),
      (∀ i, ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H i ∧ IsCyclic C ∧ (Nat.card C).Coprime q ∧
        (∀ h ∈ H i, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H i, ∃ n : ℕ, h ^ q ^ n ∈ C)) ∧
      ∀ g : G, (1 : ℚ) = ∑ i, (a i : ℚ) * ClassFunction.induced (H i) (fun _ => (1 : ℚ)) g := by p2m_exact_reverting @_root_.P2MW.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.solution
