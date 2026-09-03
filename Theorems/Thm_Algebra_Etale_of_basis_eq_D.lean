import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_of_basis_eq_D

set_option autoImplicit false

open KaehlerDifferential

universe u v

theorem Algebra.Etale.of_basis_eq_D
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    {ι : Type v} [Finite ι] (x : ι → S) (b : Module.Basis ι S Ω[S⁄R]) (hb : ∀ i, b i = D R S (x i))
    [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]
    (hx : ∀ i, algebraMap (MvPolynomial ι R) S (MvPolynomial.X i) = x i) :
    Algebra.Etale (MvPolynomial ι R) S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_of_basis_eq_D.solution
