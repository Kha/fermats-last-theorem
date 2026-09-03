import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_finite_setOf_isRamifiedIn

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

attribute [-instance] NumberField.RingOfIntegers.instAlgebra in
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    {v : HeightOneSpectrum (𝓞 ℚ) | IsRamifiedIn K v}.Finite := by
  classical
  haveI : Algebra.IsAlgebraic (FractionRing (𝓞 ℚ)) (FractionRing (𝓞 K)) :=
    isAlgebraic_of_isFractionRing (R := 𝓞 ℚ) (S := 𝓞 K) ..
  haveI : Algebra.IsSeparable (FractionRing (𝓞 ℚ)) (FractionRing (𝓞 K)) := inferInstance
  have hD : differentIdeal (𝓞 ℚ) (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hfinK : {𝔓 : HeightOneSpectrum (𝓞 K) | 𝔓.asIdeal ∣ differentIdeal (𝓞 ℚ) (𝓞 K)}.Finite :=
    Ideal.finite_factors hD
  refine (hfinK.image fun 𝔓 => 𝔓.under (𝓞 ℚ)).subset ?_
  rintro v ⟨𝔓, h𝔓, hne⟩
  refine ⟨𝔓, ?_, (LanglandsTunnell.RankinSelberg.mem_primeFibre ℚ v 𝔓).mp h𝔓⟩
  show 𝔓.asIdeal ∣ differentIdeal (𝓞 ℚ) (𝓞 K)
  by_contra hndvd
  haveI : Algebra.IsUnramifiedAt (𝓞 ℚ) 𝔓.asIdeal := not_dvd_differentIdeal_iff.mp hndvd
  have h1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 ℚ) (p := 𝔓.asIdeal)
  apply hne
  have hv : v.asIdeal = 𝔓.asIdeal.under (𝓞 ℚ) := by
    rw [← (LanglandsTunnell.RankinSelberg.mem_primeFibre ℚ v 𝔓).mp h𝔓]
    rfl
  rw [hv, Ideal.ramificationIdx'_eq_ramificationIdx (𝔓.asIdeal.under (𝓞 ℚ)) 𝔓.asIdeal (hv ▸ v.ne_bot)]
  exact h1
