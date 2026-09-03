import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_jointly_injective
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec CuspForm.HeckeGaloisRepDatum.mk.sizeOf_spec CuspForm.HeckeGaloisRepDatum.mk.injEq CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_jointly_injective
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (maximalIdeal T) T] [Finite (ResidueField T)]
    {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Algebra T (A i)] [∀ i, Module.Finite T (A i)]
    [hloc : ∀ i, IsLocalHom (algebraMap T (A i))]
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0)
    (ρbar : ResidualGaloisRep (ResidueField T)) (habs : ρbar.IsAbsolutelyIrreducible)
    (ρ : ∀ i, GaloisRepAdic (A i))
    (hres : ∀ i, (ρ i).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap T (A i)))))
    (S₀ : Finset ℕ) (τ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → T)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          ∀ i, (ρ i).trace σ = algebraMap T (A i) (τ ℓ hℓ hℓS)) :
    ∃ ρ' : GaloisRepAdic T,

      (∀ i, ((ρ'.baseChangeAlong (algebraMap T (A i)) (hloc i)).IsEquiv (ρ i))) ∧

      ρ'.residual.IsEquiv ρbar ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
            ρ'.trace σ = τ ℓ hℓ hℓS) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_jointly_injective.solution
