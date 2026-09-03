import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq
set_option autoImplicit false
open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) :
    Ideal.span {const (π ^ E) π, U (π ^ E)} ⊓ Ideal.span {const (π ^ E) π, V (π ^ E)}
        = Ideal.span {const (π ^ E) π} ∧
    (∀ n : ℕ, V (π ^ E) ^ n ∉ Ideal.span {const (π ^ E) π, U (π ^ E)}) ∧
    (∀ n : ℕ, U (π ^ E) ^ n ∉ Ideal.span {const (π ^ E) π, V (π ^ E)}) ∧
    (⨅ n : ℕ, Ideal.span {const (π ^ E) π, U (π ^ E)} ⊔ Ideal.span {V (π ^ E) ^ n})
        = Ideal.span {const (π ^ E) π, U (π ^ E)} ∧
    (⨅ n : ℕ, Ideal.span {const (π ^ E) π, V (π ^ E)} ⊔ Ideal.span {U (π ^ E) ^ n})
        = Ideal.span {const (π ^ E) π, V (π ^ E)} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq.solution
