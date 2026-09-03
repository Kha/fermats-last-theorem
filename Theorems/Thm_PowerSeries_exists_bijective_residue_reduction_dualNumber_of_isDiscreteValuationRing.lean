import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing

set_option autoImplicit false

open IsLocalRing

theorem PowerSeries.exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing
    (O : Type) [CommRing O] [IsLocalRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ∃ (ι₀ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (0 + 1)) →+* ResidueField O) (hι₀ : Function.Bijective ι₀)
      (hι₀O : ι₀.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (0 + 1))).comp (algebraMap O (PowerSeries O))) = residue O)
      (π : ∀ n : ℕ, (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1 + 1)) →+* (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1)))
      (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1 + 1))) = Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1)))
      (τ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (1 + 1)) →+* DualNumber (ResidueField O)),
      τ.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))).comp (algebraMap O (PowerSeries O))) =
          (algebraMap (ResidueField O) (DualNumber (ResidueField O))).comp (residue O) ∧
      τ (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) PowerSeries.X) = DualNumber.eps ∧
      Function.Surjective τ ∧
      RingHom.ker τ * (maximalIdeal (PowerSeries O)).map (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))) = ⊥ ∧
      (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom.comp τ = ι₀.comp (π 0) ∧
      ∀ τ' : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (1 + 1)) →+* DualNumber (ResidueField O),
        τ'.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))).comp (algebraMap O (PowerSeries O))) =
            (algebraMap (ResidueField O) (DualNumber (ResidueField O))).comp (residue O) →
        τ' (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) PowerSeries.X) = DualNumber.eps →
        τ' = τ := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing.solution
