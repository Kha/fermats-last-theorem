import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicComplex_TateTrace
import P2M.Util
import P2M.Sol.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace

set_option autoImplicit false

theorem PadicComplex.bijOn_towerClosure_smul_sub_mul_of_isTateTrace
    (p : ℕ) [Fact p.Prime] (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
    (hfin : ∀ n, FiniteDimensional ℚ_[p] (Km n))
    (m : ℕ) (d : ℝ) (R : ℂ_[p] → ℂ_[p]) (hR : PadicComplex.IsTateTrace p Km m d R)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : σ ∈ (Km m).fixingSubgroup)
    (hσ' : σ ∉ (Km (m + 1)).fixingSubgroup) (hstab : ∀ n, ∀ y ∈ Km n, σ y ∈ Km n)
    (μ : ℚ_[p]) (hμ : μ ≠ 1) (hμd : ‖μ - 1‖ * d < 1) :
    Set.BijOn (fun x : ℂ_[p] => σ • x - algebraMap ℚ_[p] ℂ_[p] μ * x)
      (PadicComplex.towerClosure p Km) (PadicComplex.towerClosure p Km) := by p2m_exact_reverting @_root_.P2MW.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace.solution
