import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing

set_option autoImplicit false

theorem IsLocalRing.isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀]
    (K₀ : Type*) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [Algebra R₀ B] [Module.Finite R₀ B]
    (hdim : ringKrullDim B ≤ (2 : WithBot ℕ∞))
    (F : Type*) [CommRing F] [Algebra B F] [Algebra R₀ F] [Algebra K₀ F]
    [IsScalarTower R₀ B F] [IsScalarTower R₀ K₀ F]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) F]
    (hinj : Function.Injective (algebraMap B F))
    [IsReduced F] [Algebra.IsSeparable K₀ F]
    (hR1 : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ¬ 𝔭.IsMaximal →
      IsRegularLocalRing (Localization.AtPrime 𝔭))
    (a b : B) (hab : RingTheory.Sequence.IsRegular B [a, b]) :
    IsDomain B ∧ IsIntegrallyClosed B ∧ IsField F ∧ IsFractionRing B F := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing.solution
