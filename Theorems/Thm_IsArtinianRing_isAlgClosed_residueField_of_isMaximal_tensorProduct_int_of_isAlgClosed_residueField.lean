import Mathlib
import P2M.Util
import P2M.Sol.S_IsArtinianRing_isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem IsArtinianRing.isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField
    (ℓ : ℕ) [Fact ℓ.Prime]
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] [CharP (ResidueField C) ℓ]
    (O : Type) [CommRing O] [IsLocalRing O] (hℓ : maximalIdeal O = Ideal.span {((ℓ : ℕ) : O)})
    (hac : IsAlgClosed (ResidueField O))
    (𝔫 : Ideal (C ⊗[ℤ] O)) [𝔫.IsMaximal] :
    IsAlgClosed 𝔫.ResidueField ∧ CharP 𝔫.ResidueField ℓ := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField.solution
