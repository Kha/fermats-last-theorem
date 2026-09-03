import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringHom_adicCompletion_of_isDiscreteValuationRing_of_maximalIdeal_eq_map_of_residueField

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_ringHom_adicCompletion_of_isDiscreteValuationRing_of_maximalIdeal_eq_map_of_residueField
    (A₀ A : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A₀ A]
    [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] [Algebra A₀ W₀] [IsLocalHom (algebraMap A₀ W₀)]

    (hW₀ : IsLocalRing.maximalIdeal W₀ = (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ W₀))
    [Module.Finite (ResidueField A₀) (ResidueField W₀)]
    [Algebra.IsSeparable (ResidueField A₀) (ResidueField W₀)]

    (χ : ResidueField W₀ →+* ResidueField A)
    (hχ : ∀ a : A₀, χ (residue W₀ (algebraMap A₀ W₀ a)) = residue A (algebraMap A₀ A a)) :
    ∃ ψ : W₀ →+* AdicCompletion (IsLocalRing.maximalIdeal A) A,
      (∀ a : A₀, ψ (algebraMap A₀ W₀ a) = algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) (algebraMap A₀ A a)) ∧
      (∀ w : W₀, w ∈ IsLocalRing.maximalIdeal W₀ → ψ w ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
      (∀ w : W₀, ∃ a : A, residue A a = χ (residue W₀ w) ∧
        ψ w - algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a ∈
          (IsLocalRing.maximalIdeal A).map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringHom_adicCompletion_of_isDiscreteValuationRing_of_maximalIdeal_eq_map_of_residueField.solution
