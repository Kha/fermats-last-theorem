import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import P2M.Util
import P2M.Sol.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq

set_option autoImplicit false

theorem PadicComplex.exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hF : ∀ (L : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F L] (x : F),
      ‖(x : PadicAlgCl p)‖ < 1 → ∃ y : L, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F L y = x)
    (c : F.fixingSubgroup → ℂ_[p]) (hc : Continuous c)
    (hcocycle : ∀ σ τ : F.fixingSubgroup,
      c (σ * τ) = c σ + (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • c τ) :
    ∃ b : ℂ_[p], ∀ σ : F.fixingSubgroup,
      c σ = (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • b - b := by p2m_exact_reverting @_root_.P2MW.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq.solution
