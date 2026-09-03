import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isClosedImmersion_of_forall_isPullback_map_of_span_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_closedImmersionBySections_of_forall_isPullback_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hf : IsProper f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (M' : ∀ i, (A' i).Modules) (e : ∀ i, (Scheme.Modules.pullback (g i)).obj M ≅ M' i)
    (h : ∀ i, Scheme.Modules.ClosedImmersionBySections (M' i) (f' i)) :
    Scheme.Modules.ClosedImmersionBySections M f  := by
  classical

  choose N' 𝔔 hQ using h
  obtain ⟨N, 𝔓, h𝔓⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_projPresentation_forall_isPullback_toProj_of_forall_away
      r hr B f f' g hg hf M hM M' e N' 𝔔
  refine ⟨N, 𝔓, ?_⟩
  choose 𝔓' hsq hspan using h𝔓
  refine AlgebraicGeometry.ProjSpace.isClosedImmersion_of_forall_isPullback_map_of_span_eq_top r hr B N 𝔓.toProj
    (fun i => (𝔓' i).toProj) g hsq fun i => ?_
  exact AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
    (𝔔 i) (𝔓' i) (hspan i) (hQ i)
