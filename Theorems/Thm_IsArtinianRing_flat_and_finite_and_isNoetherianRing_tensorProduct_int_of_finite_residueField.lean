import Mathlib
import P2M.Util
import P2M.Sol.S_IsArtinianRing_flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem IsArtinianRing.flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)]
    (O : Type) [CommRing O] [IsNoetherianRing O] [Module.Flat ℤ O] :
    Module.Flat C (C ⊗[ℤ] O) ∧ (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] C ⊗[ℤ] O).toRingHom.Finite ∧
      IsNoetherianRing (C ⊗[ℤ] O) ∧
      IsNilpotent (Ideal.map (algebraMap C (C ⊗[ℤ] O)) (maximalIdeal C)) := by p2m_exact_reverting @_root_.P2MW.S_IsArtinianRing_flat_and_finite_and_isNoetherianRing_tensorProduct_int_of_finite_residueField.solution
