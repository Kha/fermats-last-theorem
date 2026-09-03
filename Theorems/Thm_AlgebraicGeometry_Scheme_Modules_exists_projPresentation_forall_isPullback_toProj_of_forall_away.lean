import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.exists_projPresentation_forall_isPullback_toProj_of_forall_away
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hf : IsProper f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (M' : ∀ i, (A' i).Modules) (e : ∀ i, (Scheme.Modules.pullback (g i)).obj M ≅ M' i)
    (N' : Fin k → ℕ) (𝔔 : ∀ i, Scheme.Modules.ProjPresentation (M' i) (f' i) (N' i)) :
    ∃ (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation M f N),
      ∀ i, ∃ 𝔓' : Scheme.Modules.ProjPresentation (M' i) (f' i) N,
        IsPullback (g i) 𝔓'.toProj 𝔓.toProj (ProjSpace.map S (B i) N) ∧
        ∀ j : Fin (N' i + 1), ∃ a : Fin (N + 1) → B i,
          (𝔔 i).σ j = ∑ l, (((f' i).appLE ⊤ ⊤ le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of (B i))).inv.hom (a l))) • 𝔓'.σ l := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away.solution
