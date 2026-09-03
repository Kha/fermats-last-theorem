import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic

open scoped NNReal TensorProduct
open scoped TensorProduct in
theorem HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hAfin : Module.Finite ℚ A) (hAcocomm : Coalgebra.IsCocomm ℚ A)
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (hfin : Module.Finite ℤ_[p] Hp) (hflat : Module.Flat ℤ_[p] Hp)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] Hp)
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp))
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x)) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧
      Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ ψ : (ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H) ≃ₐ[ℚ] A,
        ∀ x, Coalgebra.comul (R := ℚ) (ψ x) =
          (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := ℚ) x) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic.solution
