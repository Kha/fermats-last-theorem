import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicComplex_TateTrace
import P2M.Util
import P2M.Sol.S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul

set_option autoImplicit false

open scoped TensorProduct

theorem PadicComplex.exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
    (hK : ∀ m, K ≤ Km m) (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
    (d : ℝ) (m₀ : ℕ)
    (hR : ∀ m, m₀ ≤ m → ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R)
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ψ : K.fixingSubgroup →* Lˣ)
    (hψ' : ∀ σ : K.fixingSubgroup,
      (∀ m, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (Km m).fixingSubgroup) → ψ σ = 1)
    (x : ℂ_[p] ⊗[ℚ_[p]] L) (hx : x ≠ 0)
    (hψ : ∀ σ : K.fixingSubgroup,
      Algebra.TensorProduct.map
          (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (AlgHom.id ℚ_[p] L)
          x =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : Lˣ) : L)) * x) :
    ∃ n : ℕ, 0 < n ∧ ∀ σ : K.fixingSubgroup, ψ σ ^ n = 1 := by p2m_exact_reverting @_root_.P2MW.S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul.solution
