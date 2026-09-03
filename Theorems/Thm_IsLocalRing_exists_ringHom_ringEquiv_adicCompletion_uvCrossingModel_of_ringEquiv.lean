import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_of_ringEquiv

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem IsLocalRing.exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_of_ringEquiv
    {A₀ : Type} [CommRing A₀] [IsLocalRing A₀] (ϖ₀ : A₀) (w : ℕ)
    {R : Type} [CommRing R] [IsLocalRing R] (b : A₀ →+* R)
    (e : AdicCompletion (maximalIdeal R) R ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap R (AdicCompletion (maximalIdeal R) R) (b a)) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))
    {N : Type} [CommRing N] [IsLocalRing N] (θ : R ≃+* N) :
    let Â₀ := AdicCompletion (maximalIdeal A₀) A₀
    ∃ (σ : Â₀ →+* AdicCompletion (maximalIdeal N) N)
      (ι : AdicCompletion (maximalIdeal N) N ≃+* UVCrossingModel Â₀ ((algebraMap A₀ Â₀ ϖ₀) ^ w)),
      (∀ a : A₀, σ (algebraMap A₀ Â₀ a) = algebraMap N (AdicCompletion (maximalIdeal N) N) (θ (b a))) ∧
      (∀ o : Â₀, ι (σ o) = const ((algebraMap A₀ Â₀ ϖ₀) ^ w) o) ∧
      (∀ r : R, ι (algebraMap N (AdicCompletion (maximalIdeal N) N) (θ r)) =
        e (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_of_ringEquiv.solution
