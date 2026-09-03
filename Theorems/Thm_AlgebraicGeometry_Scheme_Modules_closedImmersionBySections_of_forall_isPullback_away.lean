import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_closedImmersionBySections_of_forall_isPullback_away
attribute [-simp] AlgebraicGeometry.FramedPolarisedAbelianScheme.mk.sizeOf_spec AlgebraicGeometry.FramedPolarisedAbelianScheme.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_forall_isPullback_away
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hf : IsProper f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (M' : ∀ i, (A' i).Modules) (e : ∀ i, (Scheme.Modules.pullback (g i)).obj M ≅ M' i)
    (h : ∀ i, Scheme.Modules.ClosedImmersionBySections (M' i) (f' i)) :
    Scheme.Modules.ClosedImmersionBySections M f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_closedImmersionBySections_of_forall_isPullback_away.solution
