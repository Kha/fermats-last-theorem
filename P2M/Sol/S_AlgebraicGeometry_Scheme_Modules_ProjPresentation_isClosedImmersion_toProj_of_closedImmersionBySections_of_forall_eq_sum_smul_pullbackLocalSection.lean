import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_closedImmersionBySections_of_forall_eq_sum_smul_pullbackLocalSection

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules)
    {N : ℕ} (σ : Fin (N + 1) → Γ(M, ⊤))
    (k : Type u) [Field k] (sk : S →+* k)
    (hfib : Scheme.Modules.ClosedImmersionBySections
      ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M) (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))))
    (hspan : ∀ t : Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤),
      letI : Module k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) ⁻¹ᵁ ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) ⁻¹ᵁ ⊤) le_top).hom
      ∃ c : Fin (N + 1) → k, t = ∑ i, c i • Scheme.Modules.pullbackLocalSection (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) (σ i))
    (𝔓' : Scheme.Modules.ProjPresentation ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M) (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))) N)
    (h𝔓' : ∀ i, 𝔓'.σ i =
      (((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).unit.app M).app ⊤) (σ i)) :
    IsClosedImmersion 𝔓'.toProj := by
  obtain ⟨N', 𝔔, hQ⟩ := hfib
  refine AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul 𝔔 𝔓' (fun j => ?_) hQ
  obtain ⟨c, hc⟩ := hspan (𝔔.σ j)
  refine ⟨c, hc.trans (Finset.sum_congr rfl fun i _ => ?_)⟩
  rw [h𝔓' i]
  rfl
