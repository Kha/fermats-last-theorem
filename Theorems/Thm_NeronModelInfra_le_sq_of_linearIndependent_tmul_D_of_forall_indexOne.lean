import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import P2M.Util
import P2M.Sol.S_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne

set_option autoImplicit false

open TensorProduct KaehlerDifferential NeronModelInfra

universe u

theorem NeronModelInfra.le_sq_of_linearIndependent_tmul_D_of_forall_indexOne
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C A : Type u} [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A))
    {n : ℕ} (z : Fin n → C)
    (hIJ : RingHom.ker (algebraMap C A) ≤ Ideal.span (insert (algebraMap R C π) (Set.range z)))
    (hlin : LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
      fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
        D R A (algebraMap C A (z j)))
    (hN : ∀ g : C,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : C →ₐ[R] R'', RingHom.ker (algebraMap C A) ≤ RingHom.ker c.toRingHom →
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) →
      g ∈ Ideal.span (insert (algebraMap R C π) (Set.range z))) :
    RingHom.ker (algebraMap C A) ≤ Ideal.span (insert (algebraMap R C π) (Set.range z)) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne.solution
