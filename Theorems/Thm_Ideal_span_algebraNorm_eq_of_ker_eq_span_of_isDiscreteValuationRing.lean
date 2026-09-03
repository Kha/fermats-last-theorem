import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing

set_option autoImplicit false

universe u

theorem Ideal.span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    {K : Type u} [Field K] (χ : B →+* K) (hχ : Function.Surjective (χ.comp (algebraMap A B)))
    (g : B) (hg : RingHom.ker χ = Ideal.span {g})
    (𝔪 : Ideal A) (h𝔪 : RingHom.ker (χ.comp (algebraMap A B)) = 𝔪) [𝔪.IsMaximal]
    (Aₘ : Type u) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ 𝔪]
    [IsDomain Aₘ] [IsDiscreteValuationRing Aₘ] :
    Ideal.span {Algebra.norm A g} = 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing.solution
