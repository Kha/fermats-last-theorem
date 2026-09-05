module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
public import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ne_zero

open AlgebraicCurve IsDedekindDomain Polynomial

theorem solution {K : Type*} [Field K] (v : Place K (RatFunc K)) : v.deg ≠ 0 := by
  by_cases h : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w
  · rw [RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum v h]
    exact one_ne_zero
  · obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w := by
      simpa using h
    subst hw
    obtain ⟨p, hp⟩ := Submodule.IsPrincipal.principal w.asIdeal
    rw [RationalFunctionField.deg_ofHeightOneSpectrum K hp]
    have hp0 : p ≠ 0 := by
      intro h0
      apply w.ne_bot
      rw [hp, h0]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    have hprime : Prime p := by
      have hpr := w.isPrime
      rw [hp] at hpr
      exact (Ideal.span_singleton_prime hp0).mp hpr
    exact (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hprime.irreducible)).ne'
