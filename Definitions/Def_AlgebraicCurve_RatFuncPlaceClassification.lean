module

public import Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
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
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
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

open Polynomial IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve

namespace RationalFunctionField

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

instance instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions :
    Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass (RatFunc.inftyValuation K))) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation K RatFunc.X)
    (by rw [RatFunc.inftyValuation.X]; exact exp_ne_zero), ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · rw [ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one, RatFunc.inftyValuation.X]
    simp

theorem placeInfty_ne_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    placeInfty K ≠ Place.ofHeightOneSpectrum w := by
  intro h
  refine RatFunc.adicValuation_not_isEquiv_infty_valuation w
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr ?_)
  have h2 := congrArg Place.toValuationSubring h
  rw [placeInfty_toValuationSubring, Place.ofHeightOneSpectrum_toValuationSubring] at h2
  exact h2.symm

end PlaceInfty

variable {K}

theorem eq_ofHeightOneSpectrum_or_eq_placeInfty [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) :
    (∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact Or.inr (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)))
  · obtain ⟨w, hw, -⟩ := h
    exact Or.inl ⟨w, Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))⟩

variable (K)

theorem placeOfPoint_ne_placeInfty [DecidableEq (RatFunc K)] (a : K) :
    placeOfPoint K a ≠ placeInfty K := by
  rw [placeOfPoint_eq_ofHeightOneSpectrum]
  exact fun h => placeInfty_ne_ofHeightOneSpectrum K _ h.symm

theorem exists_eq_placeOfPoint [IsAlgClosed K] (w : HeightOneSpectrum K[X]) :
    ∃ a : K, Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = placeOfPoint K a := by
  obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
  have hdeg : p.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K hp]; exact one_ne_zero
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
  refine ⟨a, ?_⟩
  have hassoc : Associated ((X : K[X]) - C a) p :=
    (irreducible_X_sub_C a).associated_of_dvd hp (dvd_iff_isRoot.mpr ha)
  have hideal : w = heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a) :=
    HeightOneSpectrum.ext (by
      rw [hwp, heightOneSpectrumOfIrreducible_asIdeal]
      exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm)
  rw [hideal, placeOfPoint_eq_ofHeightOneSpectrum]

theorem eq_placeOfPoint_or_eq_placeInfty [IsAlgClosed K] [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) :
    (∃ a : K, v = placeOfPoint K a) ∨ v = placeInfty K := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, hw⟩ | hw
  · obtain ⟨a, ha⟩ := exists_eq_placeOfPoint K w
    exact Or.inl ⟨a, hw.trans ha⟩
  · exact Or.inr hw

def ofOption_aux [DecidableEq (RatFunc K)] : Option K → Place K (RatFunc K) :=
  fun o => o.elim (placeInfty K) (placeOfPoint K)

theorem ofOption_bijective_aux [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    Function.Bijective (ofOption_aux K) := by
  constructor
  · rintro (_ | a) (_ | b) h
    · rfl
    · exact absurd h.symm (placeOfPoint_ne_placeInfty K b)
    · exact absurd h (placeOfPoint_ne_placeInfty K a)
    · exact congrArg some (placeOfPoint_injective K h)
  · intro v
    rcases eq_placeOfPoint_or_eq_placeInfty K v with ⟨a, ha⟩ | ha
    · exact ⟨some a, ha.symm⟩
    · exact ⟨none, ha.symm⟩

def placeEquivOption [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    Place K (RatFunc K) ≃ Option K :=
  (Equiv.ofBijective (ofOption_aux K) (ofOption_bijective_aux K)).symm

@[simp]
theorem placeEquivOption_symm_some [IsAlgClosed K] [DecidableEq (RatFunc K)] (a : K) :
    (placeEquivOption K).symm (some a) = placeOfPoint K a := rfl

@[simp]
theorem placeEquivOption_symm_none [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    (placeEquivOption K).symm none = placeInfty K := rfl

@[simp]
theorem placeEquivOption_placeOfPoint [IsAlgClosed K] [DecidableEq (RatFunc K)] (a : K) :
    placeEquivOption K (placeOfPoint K a) = some a :=
  (Equiv.ofBijective (ofOption_aux K) (ofOption_bijective_aux K)).symm_apply_apply (some a)

@[simp]
theorem placeEquivOption_placeInfty [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    placeEquivOption K (placeInfty K) = none :=
  (Equiv.ofBijective (ofOption_aux K) (ofOption_bijective_aux K)).symm_apply_apply none

end RationalFunctionField

end AlgebraicCurve
