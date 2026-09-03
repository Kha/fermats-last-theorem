import Mathlib
import P2M.Util
import P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter

set_option autoImplicit false

open scoped MatrixGroups

open scoped Classical in

theorem BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter
    {G : Type} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
          ∑ x : G, if hx : x⁻¹ * g * x ∈ H i then (((ψ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0) := by p2m_exact_reverting @_root_.P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.solution
