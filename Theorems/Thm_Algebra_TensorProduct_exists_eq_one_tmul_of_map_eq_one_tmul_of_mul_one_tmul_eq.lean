import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_exists_eq_one_tmul_of_map_eq_one_tmul_of_mul_one_tmul_eq
set_option Elab.async false
set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.TensorProduct.exists_eq_one_tmul_of_map_eq_one_tmul_of_mul_one_tmul_eq
    (R : Type) [CommRing R] [IsDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (H : Type) [CommRing H] [Algebra R H]
    (e f : H) (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (hfe : f * e = e)
    (hdiv : ∀ d : R, d ≠ 0 → ∀ y : H, ∃ z : H, d • (z * (1 - e)) = y * (1 - e))
    (S : Type) [CommRing S] [Algebra R S]
    (πf : H →ₐ[R] S) (hπf : Function.Surjective πf) (hkerf : RingHom.ker πf = Ideal.span {1 - e})
    (β : K ⊗[R] H) (hβf : β * ((1 : K) ⊗ₜ[R] f) = β)
    (a : S) (hβa : Algebra.TensorProduct.map (AlgHom.id K K) πf β = (1 : K) ⊗ₜ[R] a) :
    ∃ h : H, β = (1 : K) ⊗ₜ[R] h ∧ πf h = a := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_exists_eq_one_tmul_of_map_eq_one_tmul_of_mul_one_tmul_eq.solution
