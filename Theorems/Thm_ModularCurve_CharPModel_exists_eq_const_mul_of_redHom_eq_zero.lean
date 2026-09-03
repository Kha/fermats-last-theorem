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
import P2M.Sol.S_ModularCurve_CharPModel_exists_eq_const_mul_of_redHom_eq_zero

set_option autoImplicit false
theorem ModularCurve.CharPModel.exists_eq_const_mul_of_redHom_eq_zero
    {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    {k : Type*} [Field k] (red : A →+* k)
    {E : Type*} [CommRing E] (φ : A →+* E) (X Y : E)
    (P : Polynomial (Polynomial A)) (hP : P.Monic) (hn : 0 < P.natDegree)
    (hrel : P.eval₂ (Polynomial.eval₂RingHom φ X) Y = 0)
    (R : Subring E) (hφ : ∀ a : A, φ a ∈ R) (hXR : X ∈ R) (hYR : Y ∈ R)
    (hRle : R ≤ Subring.closure (Set.range φ ∪ {X, Y}))
    {S : Type*} [Field S] [Algebra k S] (red₀ : R →+* S)
    (hcompat : ∀ a : A, red₀ ⟨φ a, hφ a⟩ = algebraMap k S (red a))
    (hX : Transcendental k (red₀ ⟨X, hXR⟩))
    (hdeg : (IntermediateField.adjoin k {red₀ ⟨X, hXR⟩}).relfinrank
      (IntermediateField.adjoin k {red₀ ⟨X, hXR⟩, red₀ ⟨Y, hYR⟩}) = P.natDegree)
    (r : R) (hr : red₀ r = 0) :
    ∃ m : A, red m = 0 ∧ ∃ r' : R, r = ⟨φ m, hφ m⟩ * r' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CharPModel_exists_eq_const_mul_of_redHom_eq_zero.solution
