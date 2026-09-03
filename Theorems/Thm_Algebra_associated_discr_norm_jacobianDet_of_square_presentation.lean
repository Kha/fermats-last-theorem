import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_Algebra_associated_discr_norm_jacobianDet_of_square_presentation

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.associated_discr_norm_jacobianDet_of_square_presentation
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {A : Type} [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A)
    {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (e : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ≃ₐ[R] A) :
    Associated (Algebra.discr R b) (Algebra.norm R (e (Ideal.Quotient.mk _ (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))))) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_associated_discr_norm_jacobianDet_of_square_presentation.solution
