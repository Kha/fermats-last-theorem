import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow

set_option autoImplicit false

open NumberField

theorem NumberField.exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow
    (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (a : ℕ) :
    ∃ (k : ℕ) (L : IntermediateField K (CyclotomicField (p ^ k) K)),
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧ Module.finrank K L = p ^ a := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow.solution
