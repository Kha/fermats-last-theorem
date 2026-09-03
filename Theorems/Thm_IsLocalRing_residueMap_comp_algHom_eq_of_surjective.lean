import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_residueMap_comp_algHom_eq_of_surjective

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.residueMap_comp_algHom_eq_of_surjective
    (Λ : Type) [CommRing Λ] (k : Type) [Field k] (res₀ : Λ →+* k) (hres₀ : Function.Surjective res₀)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra Λ A]
    (rA : A →+* k) (hkerA : RingHom.ker rA = maximalIdeal A) (hrA : ∀ w : Λ, rA (algebraMap Λ A w) = res₀ w)
    (B : Type) [CommRing B] [Algebra Λ B] (rB : B →+* k) (hrB : ∀ w : Λ, rB (algebraMap Λ B w) = res₀ w)
    (Φ : A →ₐ[Λ] B) : ∀ a : A, rB (Φ a) = rA a := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_residueMap_comp_algHom_eq_of_surjective.solution
