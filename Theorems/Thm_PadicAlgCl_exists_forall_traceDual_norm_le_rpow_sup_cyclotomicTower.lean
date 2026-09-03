import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import P2M.Util
import P2M.Sol.S_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower

set_option autoImplicit false

theorem PadicAlgCl.exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ z : IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
          (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right,
        (∀ w : IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
            (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right,
          ‖(w : PadicAlgCl p)‖ ≤ 1 →
          ‖((Algebra.trace ↥(K ⊔ PadicAlgCl.cyclotomicTower p n)
              ↥(IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
                (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right) (z * w) :
                ↥(K ⊔ PadicAlgCl.cyclotomicTower p n)) : PadicAlgCl p)‖ ≤ 1) →
        ‖(z : PadicAlgCl p)‖ ≤ (p : ℝ) ^ ε := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower.solution
