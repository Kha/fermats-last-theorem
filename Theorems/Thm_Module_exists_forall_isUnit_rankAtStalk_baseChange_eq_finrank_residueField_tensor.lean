import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (𝔭 : PrimeSpectrum R) (g : R) (hg : g ∉ 𝔭.asIdeal)
    (hproj : ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) → Module.Projective A (A ⊗[R] M)) :
    ∃ g' : R, g' ∉ 𝔭.asIdeal ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g') → IsUnit (algebraMap R A g)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g') →
        ∀ 𝔮 : PrimeSpectrum A,
          Module.rankAtStalk (A ⊗[R] M) 𝔮 =
            Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] M) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor.solution
