import Mathlib
import P2M.Util
import P2M.Sol.S_Coalgebra_exists_finiteDimensional_le_comul_mem_span

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Coalgebra.exists_finiteDimensional_le_comul_mem_span
    {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (K : Submodule k C)
    (hK : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : C ⊗[k] C | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (x : C) (hx : x ∈ K) :
    ∃ D : Submodule k C, D ≤ K ∧ FiniteDimensional k ↥D ∧ x ∈ D ∧
      ∀ y ∈ D, Coalgebra.comul (R := k) y ∈
        Submodule.span k {t : C ⊗[k] C | ∃ a ∈ D, ∃ b ∈ D, t = a ⊗ₜ[k] b} := by p2m_exact_reverting @_root_.P2MW.S_Coalgebra_exists_finiteDimensional_le_comul_mem_span.solution
