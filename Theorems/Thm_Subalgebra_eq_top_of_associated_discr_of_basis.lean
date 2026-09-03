import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_eq_top_of_associated_discr_of_basis

set_option autoImplicit false
theorem Subalgebra.eq_top_of_associated_discr_of_basis
    {R A ι : Type} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
    (b' : Module.Basis ι R A) (B : Subalgebra R A) (b : Module.Basis ι R ↥B)
    (hdiscr : Associated (Algebra.discr R (fun i => ((b i : ↥B) : A))) (Algebra.discr R b'))
    (hne : Algebra.discr R b' ≠ 0) : B = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_eq_top_of_associated_discr_of_basis.solution
