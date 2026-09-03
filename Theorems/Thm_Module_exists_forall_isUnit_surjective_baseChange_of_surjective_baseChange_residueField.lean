import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import P2M.Util
import P2M.Sol.S_Module_exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField
    {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (𝔭 : PrimeSpectrum R)
    (hf : Function.Surjective (f.baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        Function.Surjective (f.baseChange A) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField.solution
