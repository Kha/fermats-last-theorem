import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_basis_coe_eq_of_isAdicComplete_of_isHausdorff_of_isSMulRegular

set_option autoImplicit false

universe u v w

theorem Module.exists_basis_coe_eq_of_isAdicComplete_of_isHausdorff_of_isSMulRegular
    {A : Type u} [CommRing A] (π : A) [IsAdicComplete (Ideal.span {π}) A]
    {M : Type v} [AddCommGroup M] [Module A M] [IsHausdorff (Ideal.span {π}) M]
    (hπ : IsSMulRegular M π) {ι : Type w} [Finite ι]
    (b : Module.Basis ι (A ⧸ Ideal.span {π}) (M ⧸ (Ideal.span {π} • ⊤ : Submodule A M)))
    (e : ι → M) (he : ∀ i, Submodule.Quotient.mk (e i) = b i) :
    ∃ b' : Module.Basis ι A M, ⇑b' = e := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_basis_coe_eq_of_isAdicComplete_of_isHausdorff_of_isSMulRegular.solution
