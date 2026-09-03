import Mathlib
import P2M.Util
import P2M.Sol.S_Module_finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct

set_option autoImplicit false

universe u v w

open TensorProduct

theorem Module.finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct
    {R : Type u} [CommRing R] (W : Type v) [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W]
    (M : Type w) [AddCommGroup M] [Module R M]
    [Module.Finite W (W ⊗[R] M)] [Module.FaithfullyFlat W (W ⊗[R] M)] :
    Module.Finite R M ∧ Module.FaithfullyFlat R M := by p2m_exact_reverting @_root_.P2MW.S_Module_finite_and_faithfullyFlat_of_faithfullyFlat_tensorProduct.solution
