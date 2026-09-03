import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff

set_option autoImplicit false

universe u v

open scoped TensorProduct

theorem LinearMap.isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
    {m : ℕ} (u : (Fin m → A) →ₗ[A] M) :
    IsOpen {𝔭 : PrimeSpectrum A | Function.Bijective (u.baseChange 𝔭.asIdeal.ResidueField)} ∧
    ∀ (B : Type u) [CommRing B] [Algebra A B],
      Function.Bijective (u.baseChange B) ↔
        Set.range (PrimeSpectrum.comap (algebraMap A B)) ⊆
          {𝔭 : PrimeSpectrum A | Function.Bijective (u.baseChange 𝔭.asIdeal.ResidueField)} := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_isOpen_setOf_bijective_baseChange_residueField_and_forall_bijective_baseChange_iff.solution
