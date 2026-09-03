import Definitions.Def_ModularCurve_UniformizedHeckeCurve
import P2M.Util
import P2M.Sol.S_ModularCurve_UniformizedHeckeCurve_exists_mul_prod_smul_eq_of_forall_mem_support_corr

set_option autoImplicit false

open scoped MatrixGroups Topology
open ModularCurve
theorem ModularCurve.UniformizedHeckeCurve.exists_mul_prod_smul_eq_of_forall_mem_support_corr
    {Γ : Subgroup (GL (Fin 2) ℝ)} {Fc : Type} [Field Fc] [Algebra ℂ Fc] (U : UniformizedHeckeCurve Γ Fc)
    (e : ℕ) (ℓ : Fin e → ℕ) (hℓ : ∀ j, (ℓ j).Prime) (P : Fin (e + 1) → AlgebraicCurve.Place ℂ Fc)
    (τ₀ : UpperHalfPlane) (h0 : U.pt τ₀ = P 0)
    (hstep : ∀ j : Fin e, P j.succ ∈ (U.corr (ℓ j) (hℓ j) (Finsupp.single (P j.castSucc) 1)).support)
    (hlast : P (Fin.last e) = P 0) :
    ∃ (δ : Fin e → GL (Fin 2) ℝ) (γ : GL (Fin 2) ℝ),
      (∀ j, δ j ∈ U.heckePoints (ℓ j) (hℓ j)) ∧ γ ∈ Γ ∧
      (γ * ((List.ofFn δ).reverse).prod) • τ₀ = τ₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UniformizedHeckeCurve_exists_mul_prod_smul_eq_of_forall_mem_support_corr.solution
