import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_mul_eq_and_maximalIdeal_eq_span_pair_of_ringEquiv_adicCompletion

set_option autoImplicit false

universe u

theorem ModularCurve.UVCrossingModel.exists_mul_eq_and_maximalIdeal_eq_span_pair_of_ringEquiv_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (e : AdicCompletion (IsLocalRing.maximalIdeal O) O ≃+* ModularCurve.UVCrossingModel A ϖ)
    (t : O) (ht : e (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) t) = ModularCurve.UVCrossingModel.const ϖ ϖ)
    (hmany : ¬ ((Ideal.span {t} : Ideal O).minimalPrimes).Subsingleton) :
    ∃ u v : O, u * v = t ∧ IsLocalRing.maximalIdeal O = Ideal.span {u, v} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_mul_eq_and_maximalIdeal_eq_span_pair_of_ringEquiv_adicCompletion.solution
