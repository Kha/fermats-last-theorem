import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open Polynomial

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range
    (κ : Type) [Field κ] [Finite κ] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ι : κ →+* Ω)
    (ρ : Γℚ →* GL (Fin 2) Ω) (hρ : GaloisFactorsThroughFiniteLevel ρ) (S : Finset ℕ)
    (hfrob : ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          Matrix.trace ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range ∧
            Matrix.det ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range) :
    ∃ ρ₀ : Γℚ →* GL (Fin 2) κ, GaloisFactorsThroughFiniteLevel ρ₀ ∧
      (Deformation.matrixRepresentation ρ₀).IsSemisimpleRepresentation ∧
      (∀ σ : Γℚ, ρ σ = 1 → ρ₀ σ = 1) ∧
      ∀ σ : Γℚ, (((ρ₀ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).map ι).charpoly =
        ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω).charpoly := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range.solution
