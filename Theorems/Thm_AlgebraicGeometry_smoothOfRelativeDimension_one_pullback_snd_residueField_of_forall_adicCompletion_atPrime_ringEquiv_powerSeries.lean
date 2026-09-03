import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries
    (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [IsAlgClosed (ResidueField W)]
    {S : Type} [CommRing S] [Algebra W S] [Algebra.FiniteType W S]
    (hloc : ∀ (𝔮 : Ideal S) [𝔮.IsMaximal] [𝔮.LiesOver (maximalIdeal W)],
      ∃ e : AdicCompletion (maximalIdeal (Localization.AtPrime 𝔮)) (Localization.AtPrime 𝔮) ≃+* PowerSeries W,
        ∀ a : W, e (algebraMap (Localization.AtPrime 𝔮) _
            (algebraMap S (Localization.AtPrime 𝔮) (algebraMap W S a))) = PowerSeries.C a) :
    SmoothOfRelativeDimension 1
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap W S)))
        (Spec.map (CommRingCat.ofHom (algebraMap W (ResidueField W))))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_pullback_snd_residueField_of_forall_adicCompletion_atPrime_ringEquiv_powerSeries.solution
