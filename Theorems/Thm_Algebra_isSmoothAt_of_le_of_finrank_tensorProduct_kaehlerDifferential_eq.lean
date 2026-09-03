import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) [Algebra.IsSmoothAt R q]
    (h : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) =
      Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R])) :
    Algebra.IsSmoothAt R p := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isSmoothAt_of_le_of_finrank_tensorProduct_kaehlerDifferential_eq.solution
