import Mathlib
import P2M.Util
import P2M.Sol.S_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

theorem KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
    {R C A R' : Type u} [CommRing R] [CommRing C] [CommRing A] [CommRing R']
    [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A))
    [Algebra A R'] [Algebra C R'] [IsScalarTower C A R'] :
    Nonempty ((R' ⊗[A] Ω[A⁄R]) ≃ₗ[R']
      ((R' ⊗[C] Ω[C⁄R]) ⧸ Submodule.span R'
        (Set.range fun f : RingHom.ker (algebraMap C A) => (1 : R') ⊗ₜ[C] D R C (f : C)))) := by p2m_exact_reverting @_root_.P2MW.S_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective.solution
