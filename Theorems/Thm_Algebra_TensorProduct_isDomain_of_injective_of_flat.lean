import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_isDomain_of_injective_of_flat

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.TensorProduct.isDomain_of_injective_of_flat
    (R k A K : Type*) [CommRing R] [CommRing k] [Algebra R k] [Module.Flat R k]
    [CommRing A] [Algebra R A] [CommRing K] [Algebra R K]
    (f : A →ₐ[R] K) (hf : Function.Injective f) [IsDomain (k ⊗[R] K)] :
    IsDomain (k ⊗[R] A) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_isDomain_of_injective_of_flat.solution
