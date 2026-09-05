module

public import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
public import Definitions.Def_ModularCurve_PlaceSpecialization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve

namespace PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

def redFst (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    Place k (modularFunctionFieldC k 1) :=
  P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα)

def redSnd (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    Place k (modularFunctionFieldC k 1) :=
  P.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ)

def IsStrictTypeOne (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  frobOnPlacesGeomLevel k 1 data hKr (P.redFst W) = P.redSnd W ∧
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W))
      ≠ P.redFst W

def IsStrictTypeTwo (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) ∧
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W))
      ≠ P.redSnd W

def IsGoodDivisor (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : Prop :=
  ∀ W ∈ D.support, P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W

open Classical in

def fstPart (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) :=
  D.filter P.IsStrictTypeOne

open Classical in

def sndPart (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) :=
  D.filter P.IsStrictTypeTwo

def branchDegrees (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : ℤ × ℤ :=
  (Divisor.degree (P.fstPart D), Divisor.degree (P.sndPart D))

def levelOneGlueData
    (S : Finset (Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    GluingData k (modularFunctionFieldC k 1) S :=
  (Finsupp.mapDomain P.redFst (P.fstPart D), Finsupp.mapDomain P.redSnd (P.sndPart D), 0)

def IsLevelOneGluedSpecialization
    (S : Finset (Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)))
    (sp : ↥(inertiaInvariants A (1 * q)) →+ GluedPic0 k (modularFunctionFieldC k 1) S) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hH : Pic0.mk D ∈ inertiaInvariants A (1 * q))
    (x : ↥(GluingData.admissible S)),
    P.IsGoodDivisor (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) →
    (x : GluingData k (modularFunctionFieldC k 1) S) = P.levelOneGlueData S D →
      sp ⟨Pic0.mk D, hH⟩ = GluedPic0.mk S x

end PlaceSpecialization

end ModularCurve

end
