import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidAlgebra_surjective_of_surjective_residueField_comp

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped TensorProduct

theorem AddMonoidAlgebra.surjective_of_surjective_residueField_comp
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H : Type u} [CommRing H] [Algebra R H]
    (M : Type v) [AddCommMonoid M] [Finite M]
    (ψ : H →ₐ[R] AddMonoidAlgebra R M)
    (ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] AddMonoidAlgebra (ResidueField R) M)
    (hψ₀ : Function.Surjective ψ₀)
    (hred : (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp ψ =
      (ψ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight) :
    Function.Surjective ψ := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidAlgebra_surjective_of_surjective_residueField_comp.solution
