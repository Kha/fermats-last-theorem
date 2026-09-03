import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicAlgCl_CyclotomicTower
import P2M.Util
import P2M.Sol.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower

set_option autoImplicit false

theorem PadicComplex.exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (c : (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n).fixingSubgroup → ℂ_[p]) (hc : Continuous c)
    (hcocycle : ∀ σ τ : (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n).fixingSubgroup,
      c (σ * τ) = c σ + (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • c τ) :
    ∃ b : ℂ_[p], ∀ σ : (K ⊔ ⨆ n : ℕ, PadicAlgCl.cyclotomicTower p n).fixingSubgroup,
      c σ = (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • b - b := by p2m_exact_reverting @_root_.P2MW.S_PadicComplex_exists_eq_smul_sub_of_continuous_cocycle_fixingSubgroup_sup_cyclotomicTower.solution
