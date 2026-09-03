import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range
import Theorems.Thm_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic
import P2M.Util
namespace P2MW.S_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_basis_match

open scoped NNReal TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hAfin : Module.Finite ℚ A) (hAcocomm : Coalgebra.IsCocomm ℚ A)
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (hfin : Module.Finite ℤ_[p] Hp) (hflat : Module.Flat ℤ_[p] Hp)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] Hp)
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp))
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x))
    (n : ℕ) (b : Module.Basis (Fin n) ℚ A) (bHp : Module.Basis (Fin n) ℤ_[p] Hp)
    (hmatch : ∀ i, φ (1 ⊗ₜ[ℚ] (b i)) = 1 ⊗ₜ[ℤ_[p]] (bHp i)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ ψ : (ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H) ≃ₐ[ℚ] A,
        ∀ x, Coalgebra.comul (R := ℚ) (ψ x) =
          (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := ℚ) x) := by
  have := hAfin; have := hfin; have := hflat; have := hcocomm
  obtain ⟨hmul, hone, hcomul, hcounit, hanti⟩ :=
    HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic
      p A Hp φ hφcomul n b bHp hmatch
  haveI : IsFractionRing (GaloisRep.ratLocalizedAt p) ℚ :=
    GaloisRep.isFractionRing_ratLocalizedAt p
  exact HopfAlgebra.exists_hopfOrder_of_basis_structureConstants_mem_range
    (GaloisRep.ratLocalizedAt p) ℚ (IsFractionRing.injective _ _) A hAcocomm n b
    hmul hone hcomul hcounit hanti
