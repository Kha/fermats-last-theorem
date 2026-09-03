import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth

set_option autoImplicit false

universe u

theorem Algebra.IsSmoothAt.of_isSmoothAt_of_smooth (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.FinitePresentation R S] [Algebra.Smooth S T] (𝔓 : Ideal T) [𝔓.IsPrime]
    (h : Algebra.IsSmoothAt R 𝔓) (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔓.under S = 𝔭) :
    Algebra.IsSmoothAt R 𝔭 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth.solution
