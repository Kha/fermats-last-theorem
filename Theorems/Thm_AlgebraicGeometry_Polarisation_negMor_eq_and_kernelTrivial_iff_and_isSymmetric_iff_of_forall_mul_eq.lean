import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_negMor_eq_and_kernelTrivial_iff_and_isSymmetric_iff_of_forall_mul_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

universe u

theorem AlgebraicGeometry.Polarisation.negMor_eq_and_kernelTrivial_iff_and_isSymmetric_iff_of_forall_mul_eq
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L' L'' : RelativeGroupLaw S f)
    (h : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      L'.mul t P Q = L''.mul t P Q) :
    negMor f L' = negMor f L'' ∧
    (∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)), L'.one t = L''.one t) ∧
    (∀ 𝓜 : A.Modules, KernelTrivial f L' 𝓜 ↔ KernelTrivial f L'' 𝓜) ∧
    (∀ 𝓜 : A.Modules, IsSymmetric f L' 𝓜 ↔ IsSymmetric f L'' 𝓜) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_negMor_eq_and_kernelTrivial_iff_and_isSymmetric_iff_of_forall_mul_eq.solution
