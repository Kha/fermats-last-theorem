import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.isUnramifiedAt_iff_isUnramifiedAt_fiber
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.EssFiniteType R A]
    (P : Ideal R) [P.IsPrime] (Q : Ideal A) [Q.IsPrime] [Q.LiesOver P]
    (Q' : Ideal (P.Fiber A)) [Q'.IsPrime]
    (hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    Algebra.IsUnramifiedAt R Q ↔ Algebra.IsUnramifiedAt P.ResidueField Q' := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber.solution
