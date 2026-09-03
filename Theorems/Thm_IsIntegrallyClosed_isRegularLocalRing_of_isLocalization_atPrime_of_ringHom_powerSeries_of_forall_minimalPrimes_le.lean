import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_isRegularLocalRing_of_isLocalization_atPrime_of_ringHom_powerSeries_of_forall_minimalPrimes_le

theorem IsIntegrallyClosed.isRegularLocalRing_of_isLocalization_atPrime_of_ringHom_powerSeries_of_forall_minimalPrimes_le
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {Λ : Type*} [CommRing Λ] [IsDomain Λ] [Algebra A Λ] [FaithfulSMul A Λ]
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] [Algebra A B]
    (ι : B →+* PowerSeries Λ) (χ : B →+* A)
    (hχ : ∀ b : B, algebraMap A Λ (χ b) = PowerSeries.constantCoeff (ι b))
    (hιC : ∀ a : A, ι (algebraMap A B a) = PowerSeries.C (algebraMap A Λ a))
    (u : B) (hu : ∃ w : PowerSeries Λ, IsUnit w ∧ ι u = PowerSeries.X * w)
    (𝔫 : Ideal B) [𝔫.IsPrime]
    (h𝔫 : ∀ b : B, b ∈ 𝔫 ↔ χ b ∈ IsLocalRing.maximalIdeal A)
    (hmin : ∀ P ∈ (Ideal.span {u}).minimalPrimes, P ≤ 𝔫 → P = RingHom.ker χ)
    (ϖ : A) (hϖ : Irreducible ϖ)
    (Bm : Type*) [CommRing Bm] [Algebra B Bm] [IsLocalization.AtPrime Bm 𝔫] :
    IsRegularLocalRing Bm ∧ ringKrullDim Bm = 2 ∧
      𝔫.map (algebraMap B Bm) =
        Ideal.span {algebraMap B Bm (algebraMap A B ϖ), algebraMap B Bm u} := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_isRegularLocalRing_of_isLocalization_atPrime_of_ringHom_powerSeries_of_forall_minimalPrimes_le.solution
