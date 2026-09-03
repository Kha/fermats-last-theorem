import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_IsOpen_exists_numberField_ker_restrictNormalHom_le
import Theorems.Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker
import P2M.Util
namespace P2MW.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

theorem solution
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H := by

  obtain ⟨F, hF, hNF, hGal, hAlg, hST, hker⟩ :=
    hH.exists_numberField_ker_restrictNormalHom_le
  letI := hF; letI := hNF; letI := hGal; letI := hAlg; letI := hST

  obtain ⟨ℓ, A, τ, g, n, hℓ, hℓS, hA, hτ, hmem⟩ :=
    FrobeniusDensity.frobeniusPowerDense_of_le_ker F hker M.primeFactors σ

  exact ⟨ℓ, A, τ, g, n, hℓ,
    fun hdvd => hℓS (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, hM.ne'⟩),
    hA, hτ, hmem⟩
