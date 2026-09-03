import Mathlib
import P2M.Util
namespace P2MW.S_NumberField_InfinitePlace_exists_pow_eq_of_isTotallyComplex

set_option autoImplicit false

open NumberField

open NumberField in

theorem solution
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (w : InfinitePlace K) (u : (w.Completion)ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ v : (w.Completion)ˣ, v ^ n = u := by

  let e : w.Completion ≃+* ℂ :=
    InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)

  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (u : w.Completion)) hn
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hz
    exact (e.map_ne_zero_iff.2 u.ne_zero) hz.symm
  have hv0 : e.symm z ≠ 0 := fun h => hz0 (by simpa using congrArg e h)
  refine ⟨Units.mk0 (e.symm z) hv0, Units.ext ?_⟩
  change (e.symm z) ^ n = (u : w.Completion)
  apply e.injective
  rw [map_pow, e.apply_symm_apply, hz]
