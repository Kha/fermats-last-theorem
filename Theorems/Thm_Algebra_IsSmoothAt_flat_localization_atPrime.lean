import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsSmoothAt_flat_localization_atPrime

set_option autoImplicit false

open Algebra

theorem Algebra.IsSmoothAt.flat_localization_atPrime (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (p : Ideal A) [p.IsPrime] [Algebra.IsSmoothAt R p] :
    Module.Flat R (Localization.AtPrime p) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsSmoothAt_flat_localization_atPrime.solution
