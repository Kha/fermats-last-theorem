import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallyUnramified_ext_of_isHausdorff

theorem Algebra.FormallyUnramified.ext_of_isHausdorff (R A B : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.FormallyUnramified R A] (I : Ideal B) [IsHausdorff I B] (f g : A →ₐ[R] B)
    (h : (Ideal.Quotient.mkₐ R I).comp f = (Ideal.Quotient.mkₐ R I).comp g) : f = g := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallyUnramified_ext_of_isHausdorff.solution
