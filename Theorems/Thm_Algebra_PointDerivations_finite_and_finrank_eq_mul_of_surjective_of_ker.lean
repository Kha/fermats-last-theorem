import Mathlib
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_Algebra_PointDerivations_finite_and_finrank_eq_mul_of_surjective_of_ker

set_option autoImplicit false

universe u v w w'
theorem Algebra.PointDerivations.finite_and_finrank_eq_mul_of_surjective_of_ker
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] (ev : A →+* k)
    (hev : ev.comp (algebraMap k A) = RingHom.id k)
    (Ω : Type w) [AddCommGroup Ω] [Module k Ω] [Module.Finite k Ω]
    (π : ↥((RingHom.ker ev).restrictScalars k) →ₗ[k] Ω) (hπ : Function.Surjective π)
    (hπker : ∀ x : ↥((RingHom.ker ev).restrictScalars k), π x = 0 ↔ (x : A) ∈ (RingHom.ker ev) ^ 2)
    (M : Type w') [AddCommGroup M] [Module k M] [Module.Finite k M] :
    Module.Finite k ↥(Algebra.PointDerivations k A ev M) ∧
      Module.finrank k ↥(Algebra.PointDerivations k A ev M) = Module.finrank k Ω * Module.finrank k M := by p2m_exact_reverting @_root_.P2MW.S_Algebra_PointDerivations_finite_and_finrank_eq_mul_of_surjective_of_ker.solution
