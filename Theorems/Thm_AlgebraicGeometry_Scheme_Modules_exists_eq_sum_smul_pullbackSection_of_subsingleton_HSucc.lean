import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc
attribute [-simp] TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfin : ∀ 𝒰 : X.OrderedAffineCover, (OModulePresheaf.ofModules f M).CechFinite 𝒰)
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : ∀ 𝒲 : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).OrderedAffineCover,
      Subsingleton
        ((OModulePresheaf.ofModules (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            ((Scheme.Modules.pullback
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M)).HSucc 𝒲 0))
    {k : ℕ} (τ : Fin k → Γ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M, ⊤)) :
    ∃ (N : ℕ) (m : Fin (N + 1) → Γ(M, ⊤)) (c : Fin k → Fin (N + 1) → K), ∀ i,
      τ i = ∑ j, ((Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).appTop
                    ((Scheme.ΓSpecIso (.of K)).inv (c i j))) •
        (show Γ((Scheme.Modules.pullback
                  (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M, ⊤) from
          (((Scheme.Modules.pullbackPushforwardAdjunction
            (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).unit.app M).app ⊤) (m j)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc.solution
