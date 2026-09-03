import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_away

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pos_of_forall_away
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (A' : Fin k → Scheme.{u}) (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (Localization.Away (r i))))
    (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i))))))
    (𝓛 : A.Modules)
    (hloc : ∀ (i : Fin k) (K : Type u) [Field K] [IsAlgClosed K] (sk' : Localization.Away (r i) →+* K),
      0 < Scheme.Modules.geomFibreH0Finrank (f' i) ((Scheme.Modules.pullback (g i)).obj 𝓛) K sk') :
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (sk : S →+* K), 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 K sk := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_away.solution
