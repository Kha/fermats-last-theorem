import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_GaloisRep_Adic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_finrank_inertiaFixed_eq_one_and_frobenius_sub_smul_mem_of_isEquiv_residual_of_stableLine

set_option autoImplicit false

theorem ResidualGaloisRep.exists_finrank_inertiaFixed_eq_one_and_frobenius_sub_smul_mem_of_isEquiv_residual_of_stableLine
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (q : ℕ) (hq : q.Prime) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hramP : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρbar.ρ τ ≠ 1)
    {O : Type} [CommRing O] [IsLocalRing O] (φ : k →+* IsLocalRing.ResidueField O)
    (ρ : GaloisRepAdic O) (hred : ResidualGaloisRep.IsEquiv ρ.residual (ρbar.baseChangeAlong φ))
    (L : Submodule O ρ.V) (hL : ∃ b : Module.Basis (Fin 2) O ρ.V, L = O ∙ b 0)
    (hstab : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hIL : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v ∈ L, ρ.ρ τ v = v)
    (hIQ : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L)
    (a : O) (hFrob : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
      ∀ v : ρ.V, ρ.ρ σ v - a • v ∈ L) :
    Module.finrank k ↥(⨅ τ ∈ P.inertiaSubgroupIn ℚ, Module.End.eigenspace (ρbar.ρ τ) 1) = 1 ∧
    (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρbar.V,
      ρbar.ρ τ v - v ∈ ⨅ τ' ∈ P.inertiaSubgroupIn ℚ, Module.End.eigenspace (ρbar.ρ τ') 1) ∧
    ∃ c : k, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v : ρbar.V, ρbar.ρ σ v - c • v ∈ ⨅ τ ∈ P.inertiaSubgroupIn ℚ, Module.End.eigenspace (ρbar.ρ τ) 1) ∧
      φ c = IsLocalRing.residue O a := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_finrank_inertiaFixed_eq_one_and_frobenius_sub_smul_mem_of_isEquiv_residual_of_stableLine.solution
