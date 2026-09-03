import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of (∀ i, C i))) (𝓛 : A'.Modules)
    {Ai : Fin k → Scheme.{0}} (fi : ∀ i, Ai i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Ai i ⟶ A')
    (hv : ∀ i, IsPullback (v i) (fi i) f' (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (hloc : ∀ (i : Fin k) (K : Type) [Field K] [IsAlgClosed K] (sk : C i →+* K),
      0 < Scheme.Modules.geomFibreH0Finrank (fi i) ((Scheme.Modules.pullback (v i)).obj 𝓛) K sk) :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (sk : (∀ i, C i) →+* K), 0 < Scheme.Modules.geomFibreH0Finrank f' 𝓛 K sk := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi.solution
