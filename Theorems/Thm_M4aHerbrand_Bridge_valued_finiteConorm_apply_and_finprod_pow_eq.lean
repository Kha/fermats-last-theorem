import Mathlib
import Definitions.Def_M4aHerbrand_FiniteConorm
import P2M.Util
import P2M.Sol.S_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq

set_option autoImplicit false
set_option maxSynthPendingDepth 3
open IsDedekindDomain
open scoped nonZeroDivisors

theorem M4aHerbrand.Bridge.valued_finiteConorm_apply_and_finprod_pow_eq
    (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]
    (x : (FiniteAdeleRing A K)ˣ) :
    (∀ w : HeightOneSpectrum B,
      Valued.v (((Units.map (M4aHerbrand.Bridge.finiteConorm A K L B).toMonoidHom x : (FiniteAdeleRing B L)ˣ) :
        FiniteAdeleRing B L) w) =
        Valued.v ((x : FiniteAdeleRing A K) (w.under A)) ^ (w.under A).asIdeal.ramificationIdx' w.asIdeal) ∧
    ∏ᶠ w : HeightOneSpectrum B, (w.asIdeal : FractionalIdeal B⁰ L) ^
        (-(WithZero.log (Valued.v (((Units.map (M4aHerbrand.Bridge.finiteConorm A K L B).toMonoidHom x :
          (FiniteAdeleRing B L)ˣ) : FiniteAdeleRing B L) w)))) =
      ∏ᶠ v : HeightOneSpectrum A, ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) ^
        (-(WithZero.log (Valued.v ((x : FiniteAdeleRing A K) v)))) := by p2m_exact_reverting @_root_.P2MW.S_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq.solution
