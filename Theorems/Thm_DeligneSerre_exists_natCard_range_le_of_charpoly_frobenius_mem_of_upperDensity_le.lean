import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ModularCurve.upperElem_zero ModularCurve.lowerElem_coe ModularCurve.lowerElem_zero ModularCurve.upperElem_coe

set_option autoImplicit false

open Polynomial
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
    (η : ℝ) (hη : η < 1 / 2) (M : ℕ) (X : Set ℕ)
    (hX : ∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ∑' p : {p : ℕ // p.Prime ∧ p ∈ X}, ((p : ℕ) : ℝ) ^ (-s) ≤
        (η + δ) * Real.log (1 / (s - 1))) :
    ∃ A : ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ρ : Γℚ →* GL (Fin 2) (ZMod ℓ)),
      GaloisFactorsThroughFiniteLevel ρ →
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation →
      ∀ (S : Finset ℕ) (P : Finset (ZMod ℓ)[X]), P.card ≤ M →
        (∀ p : ℕ, p.Prime → p ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : Γℚ, A.IsFrobeniusAt σ p → p ∉ X →
              ((ρ σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly ∈ P) →
        Nat.card (MonoidHom.range ρ) ≤ A := by p2m_exact_reverting @_root_.P2MW.S_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le.solution
