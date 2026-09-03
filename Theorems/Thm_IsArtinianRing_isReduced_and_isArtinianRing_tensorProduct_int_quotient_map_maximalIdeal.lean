import Mathlib
import P2M.Util
import P2M.Sol.S_IsArtinianRing_isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem IsArtinianRing.isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal
    (ℓ : ℕ) [Fact ℓ.Prime]
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] [CharP (ResidueField C) ℓ]
    (O : Type) [CommRing O] (hℓ : (Ideal.span {((ℓ : ℕ) : O)}).IsMaximal) :
    IsReduced ((C ⊗[ℤ] O) ⧸ Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) ∧
      IsArtinianRing ((C ⊗[ℤ] O) ⧸ Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) ∧
      Nontrivial ((C ⊗[ℤ] O) ⧸ Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_isReduced_and_isArtinianRing_tensorProduct_int_quotient_map_maximalIdeal.solution
