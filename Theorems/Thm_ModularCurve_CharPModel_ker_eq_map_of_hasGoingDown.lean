import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_CharPModel_ker_eq_map_of_hasGoingDown

set_option autoImplicit false
theorem ModularCurve.CharPModel.ker_eq_map_of_hasGoingDown
    {P₀ : Type*} [CommRing P₀] {B : Type*} [CommRing B] [Algebra P₀ B]
    [Algebra.IsIntegral P₀ B] [Algebra.HasGoingDown P₀ B]
    {κ : Type*} [Field κ] (π : B →+* κ) (𝔭₀ : Ideal P₀) [𝔭₀.IsPrime]
    (hK : (RingHom.ker π).comap (algebraMap P₀ B) = 𝔭₀)
    (R : Subring B) (halg : ∀ p : P₀, algebraMap P₀ B p ∈ R)
    (hpres : ∀ b : B, ∃ r ∈ R, ∃ s ∈ R, π s ≠ 0 ∧ b * s = r)
    (hfree : ∀ r ∈ R, π r = 0 → ∃ c ∈ 𝔭₀, ∃ r' ∈ R, r = algebraMap P₀ B c * r')
    (hrad : ∀ (b : B) (n : ℕ), 0 < n → b ^ n ∈ 𝔭₀.map (algebraMap P₀ B) →
      b ∈ 𝔭₀.map (algebraMap P₀ B)) :
    RingHom.ker π = 𝔭₀.map (algebraMap P₀ B) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_ker_eq_map_of_hasGoingDown.solution
