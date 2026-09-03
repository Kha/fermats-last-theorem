import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq
import Theorems.Thm_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower
import P2M.Util
namespace P2MW.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (c : (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n).fixingSubgroup → ℂ_[p]) (hc : Continuous c)
    (hcocycle : ∀ σ τ : (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n).fixingSubgroup,
      c (σ * τ) = c σ + (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • c τ) :
    ∃ b : ℂ_[p], ∀ σ : (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n).fixingSubgroup,
      c σ = (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • b - b :=
  PadicComplex.exists_eq_smul_sub_of_continuous_cocycle_of_forall_exists_trace_eq p
    (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n)
    (fun L _ x hx =>
      PadicAlgCl.exists_norm_le_one_and_trace_eq_of_norm_lt_one_sup_cyclotomicTower p K L x hx)
    c hc hcocycle
