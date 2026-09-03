import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isSmoothAt_of_isSmoothAt_fiber

set_option autoImplicit false

universe u

theorem Algebra.isSmoothAt_of_isSmoothAt_fiber
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] [Algebra.FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom = q)
    [Algebra.IsSmoothAt p.ResidueField Q] :
    Algebra.IsSmoothAt R q := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isSmoothAt_of_isSmoothAt_fiber.solution
