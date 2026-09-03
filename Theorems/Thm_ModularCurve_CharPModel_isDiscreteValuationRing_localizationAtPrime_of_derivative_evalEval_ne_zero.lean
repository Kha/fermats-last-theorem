import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Polynomial.Bivariate
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate
set_option maxSynthPendingDepth 3 in
theorem ModularCurve.CharPModel.isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero
    {k : Type*} [Field k] (P : k[X][Y]) (hP : P.Monic) (a b : k)
    (hder : (Polynomial.derivative P).evalEval a b ≠ 0)
    [hm : (Ideal.span {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
        Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)}).IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
       Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)})),
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
       Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)})) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero.solution
