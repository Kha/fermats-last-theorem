import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import P2M.Util
import P2M.Sol.S_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup

set_option autoImplicit false

theorem PadicComplex.exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup
    (p : ℕ) [Fact p.Prime] {W : Type*} [AddCommGroup W] [Module ℂ_[p] W]
    (ρ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → W →+ W)
    (hρ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (c : ℂ_[p]) (w : W),
      ρ σ (c • w) = (σ • c) • ρ σ w)
    (hρone : ∀ w : W, ρ 1 w = w)
    (hρmul : ∀ (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (w : W), ρ (σ * τ) w = ρ σ (ρ τ w))
    (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* ℂ_[p]ˣ)
    (hχ : ∀ σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ • ((χ τ : ℂ_[p]ˣ) : ℂ_[p]) = χ τ)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {ι : Type*} [Finite ι] (f : ι → (W →ₗ[ℂ_[p]] ℂ_[p])) (hf : LinearIndependent ℂ_[p] f)
    (hfK : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup →
      ∀ (i : ι) (x : W), f i (ρ σ x) = (χ σ : ℂ_[p]) * σ • f i x) :
    ∃ f' : ι → (W →ₗ[ℂ_[p]] ℂ_[p]), LinearIndependent ℂ_[p] f' ∧
      ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (i : ι) (x : W),
        f' i (ρ σ x) = (χ σ : ℂ_[p]) * σ • f' i x := by p2m_exact_reverting @_root_.P2MW.S_PadicComplex_exists_linearIndependent_forall_apply_eq_mul_smul_of_forall_mem_fixingSubgroup.solution
