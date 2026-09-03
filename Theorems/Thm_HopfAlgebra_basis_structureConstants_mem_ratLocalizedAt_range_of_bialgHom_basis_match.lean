import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match

open scoped NNReal TensorProduct
open scoped TensorProduct in
theorem HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp))
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x))
    (hφcounit : ∀ x, Coalgebra.counit (R := ℚ_[p]) (φ x) = Coalgebra.counit (R := ℚ_[p]) x)
    (hφanti : ∀ x, φ (HopfAlgebra.antipode ℚ_[p] x) = HopfAlgebra.antipode ℚ_[p] (φ x))
    (n : ℕ) (b : Module.Basis (Fin n) ℚ A) (bHp : Module.Basis (Fin n) ℤ_[p] Hp)
    (hmatch : ∀ i, φ (1 ⊗ₜ[ℚ] (b i)) = 1 ⊗ₜ[ℤ_[p]] (bHp i)) :
    (∀ i j k, b.repr (b i * b j) k ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ k, b.repr 1 k ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i jk, (b.tensorProduct b).repr (Coalgebra.comul (R := ℚ) (b i)) jk
        ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i, Coalgebra.counit (R := ℚ) (b i) ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i k, b.repr (HopfAlgebra.antipode ℚ (b i)) k
        ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match.solution
