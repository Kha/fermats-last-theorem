import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential

set_option autoImplicit false

universe u

open KaehlerDifferential

theorem Algebra.FormallySmooth.etale_aeval_of_basis_kaehlerDifferential
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Algebra.FormallySmooth R A]
    {ι : Type u} [Finite ι] (a : ι → A)
    (b : Module.Basis ι A (Ω[A⁄R])) (hb : ∀ i, b i = KaehlerDifferential.D R A (a i)) :
    (MvPolynomial.aeval a : MvPolynomial ι R →ₐ[R] A).toRingHom.Etale := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential.solution
