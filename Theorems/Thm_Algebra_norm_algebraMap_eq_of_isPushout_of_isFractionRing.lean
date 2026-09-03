import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing

set_option autoImplicit false

universe u

theorem Algebra.norm_algebraMap_eq_of_isPushout_of_isFractionRing
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsDomain A] [IsDomain B] [IsDomain A'] [IsDomain B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A B A' B']
    [Module.Finite A B] (hAB : Function.Injective (algebraMap A B)) (hA'B' : Function.Injective (algebraMap A' B'))
    (K L K' L' : Type u) [Field K] [Field L] [Field K'] [Field L']
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A' K'] [IsFractionRing A' K'] [Algebra B' L'] [IsFractionRing B' L']
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L'] [IsScalarTower A' B' L']
    (φ : K →+* K') (hφ : φ.comp (algebraMap A K) = (algebraMap A' K').comp (algebraMap A A'))
    (b : B) :
    φ (Algebra.norm K (algebraMap B L b)) = Algebra.norm K' (algebraMap B' L' (algebraMap B B' b)) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing.solution
