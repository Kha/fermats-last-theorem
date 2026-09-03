import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsUnramifiedAt_isRegularLocalRing_localization_of_ne_maximalIdeal

set_option autoImplicit false

open TensorProduct

theorem Algebra.IsUnramifiedAt.isRegularLocalRing_localization_of_ne_maximalIdeal
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    (hR : ∀ (𝔯 : Ideal R₀) [𝔯.IsPrime], 𝔯 ≠ IsLocalRing.maximalIdeal R₀ →
      IsRegularLocalRing (Localization.AtPrime 𝔯))
    (hdim : ringKrullDim R₀ ≤ (2 : WithBot ℕ∞))
    (K₀ : Type*) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    {B : Type*} [CommRing B] [IsNoetherianRing B] [Algebra R₀ B] [Module.Finite R₀ B]
    (F : Type*) [CommRing F] [Algebra B F] [Algebra R₀ F] [Algebra K₀ F]
    [IsScalarTower R₀ B F] [IsScalarTower R₀ K₀ F]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) F]
    (hinj : Function.Injective (algebraMap B F)) [IsReduced F]
    (hB : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ¬ 𝔭.IsMaximal → Algebra.IsUnramifiedAt R₀ 𝔭) :
    ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ¬ 𝔭.IsMaximal → IsRegularLocalRing (Localization.AtPrime 𝔭) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsUnramifiedAt_isRegularLocalRing_localization_of_ne_maximalIdeal.solution
