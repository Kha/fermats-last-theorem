import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_negMor_eq_and_kernelTrivial_iff_and_isSymmetric_iff_of_forall_mul_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L' L'' : RelativeGroupLaw S f)
    (h : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      L'.mul t P Q = L''.mul t P Q) :
    negMor f L' = negMor f L'' ∧
    (∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)), L'.one t = L''.one t) ∧
    (∀ 𝓜 : A.Modules, KernelTrivial f L' 𝓜 ↔ KernelTrivial f L'' 𝓜) ∧
    (∀ 𝓜 : A.Modules, IsSymmetric f L' 𝓜 ↔ IsSymmetric f L'' 𝓜) := by
  have hone : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)), L'.one t = L''.one t :=
    fun T t =>
      calc L'.one t = L''.mul t (L''.one t) (L'.one t) := (L''.one_mul t _).symm
        _ = L'.mul t (L''.one t) (L'.one t) := (h T t _ _).symm
        _ = L''.one t := L'.mul_one t _
  have hinv : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f),
      L'.inv t x = L''.inv t x := by
    intro T t x
    letI := L''.pointGroup t
    have h1 : L'.inv t x * x = 1 := by
      show L''.mul t (L'.inv t x) x = L''.one t
      rw [← h, L'.inv_mul_cancel, hone]
    exact eq_inv_of_mul_eq_one_left h1
  have hneg : negMor f L' = negMor f L'' := by
    unfold negMor
    rw [hinv]
  have hadd : addMor f L' = addMor f L'' := by
    unfold addMor
    rw [h]
  have hmb : ∀ 𝓜 : A.Modules, mumfordBundle f L' 𝓜 = mumfordBundle f L'' 𝓜 := by
    intro 𝓜
    unfold mumfordBundle
    rw [hadd]
  refine ⟨hneg, hone, fun 𝓜 => ?_, fun 𝓜 => ?_⟩
  · unfold KernelTrivial
    simp only [hmb, hone]
  · unfold IsSymmetric
    rw [hneg]
