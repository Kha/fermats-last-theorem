import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map

set_option autoImplicit false

universe u v w x

theorem Algebra.FormallySmooth.exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map
    {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    {A : Type v} {A' : Type w} {A₀ : Type x} [CommRing A] [CommRing A'] [CommRing A₀]
    [Algebra R A] [Algebra R A'] [Algebra R A₀]
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R A']
    (g : A →ₐ[R] A₀) (g' : A' →ₐ[R] A₀)
    (hg : Function.Surjective g) (hg' : Function.Surjective g')
    (hkg : RingHom.ker g = I.map (algebraMap R A)) (hkg' : RingHom.ker g' = I.map (algebraMap R A')) :
    ∃ e : A ≃ₐ[R] A', g'.comp (e : A →ₐ[R] A') = g := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_exists_algEquiv_comp_eq_of_isNilpotent_of_ker_eq_map.solution
