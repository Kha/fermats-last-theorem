import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import P2M.Util
import P2M.Sol.S_AffineDilatation_exists_algHom_surjective_ker_iff_of_surjective

set_option autoImplicit false

universe u

theorem AffineDilatation.exists_algHom_surjective_ker_iff_of_surjective
    {R : Type u} [CommRing R] (π : R)
    {C A : Type u} [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A)) (J : Ideal C) :
    ∃ θ' : AffineDilatation.Ring J (algebraMap R C π) →ₐ[C]
        AffineDilatation.Ring (J.map (algebraMap C A)) (algebraMap R A π),
      Function.Surjective θ' ∧
      ∀ x : AffineDilatation.Ring J (algebraMap R C π),
        θ' x = 0 ↔ ∃ ν : ℕ, (algebraMap R _ π) ^ ν * x ∈
          (RingHom.ker (algebraMap C A)).map (algebraMap C (AffineDilatation.Ring J (algebraMap R C π))) := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_exists_algHom_surjective_ker_iff_of_surjective.solution
