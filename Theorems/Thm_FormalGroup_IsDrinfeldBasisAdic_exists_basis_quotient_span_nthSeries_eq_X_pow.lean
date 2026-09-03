import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import P2M.Util
import P2M.Sol.S_FormalGroup_IsDrinfeldBasisAdic_exists_basis_quotient_span_nthSeries_eq_X_pow

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.IsDrinfeldBasisAdic.exists_basis_quotient_span_nthSeries_eq_X_pow
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T)
    (q : ℕ) (x₀ x₁ : T) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I)
    (hD : F.IsDrinfeldBasisAdic I q x₀ x₁) :
    ∃ b : Module.Basis (Fin (q * q)) T (PowerSeries T ⧸ Ideal.span {F.nthSeries q}),
      ∀ i, b i = Ideal.Quotient.mk (Ideal.span {F.nthSeries q}) (PowerSeries.X ^ (i : ℕ)) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_basis_quotient_span_nthSeries_eq_X_pow.solution
