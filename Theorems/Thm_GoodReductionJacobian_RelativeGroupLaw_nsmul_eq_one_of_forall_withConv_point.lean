import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_forall_withConv_point

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_forall_withConv_point
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar] [IsScalarTower R K Kbar]
    {X : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} [IsSeparated gX] (L : RelativeGroupLaw R gX)
    (H : Type u) [CommRing H] [Bialgebra R H]
    [IsReduced (Spec (CommRingCat.of H))] [Flat (Spec.map (CommRingCat.ofHom (algebraMap R H)))]
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R H)))]
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R H))) gX)
    (hone : (⟨Spec.map (CommRingCat.ofHom (1 : WithConv (H →ₐ[R] Kbar)).ofConv.toRingHom) ≫ u.1, by
        rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2; exact (1 : WithConv (H →ₐ[R] Kbar)).ofConv.comp_algebraMap⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gX) = L.one _)
    (hmul : ∀ χ χ' : WithConv (H →ₐ[R] Kbar),
      (⟨Spec.map (CommRingCat.ofHom (χ * χ').ofConv.toRingHom) ≫ u.1, by
          rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2; exact (χ * χ').ofConv.comp_algebraMap⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gX) =
        L.mul _
          ⟨Spec.map (CommRingCat.ofHom χ.ofConv.toRingHom) ≫ u.1, by
            rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            congr 2; exact χ.ofConv.comp_algebraMap⟩
          ⟨Spec.map (CommRingCat.ofHom χ'.ofConv.toRingHom) ≫ u.1, by
            rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            congr 2; exact χ'.ofConv.comp_algebraMap⟩)
    (m : ℕ) (htors : ∀ χ : WithConv (H →ₐ[R] Kbar), χ ^ m = 1) :
    L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap R H))) m u = L.one _ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_forall_withConv_point.solution
