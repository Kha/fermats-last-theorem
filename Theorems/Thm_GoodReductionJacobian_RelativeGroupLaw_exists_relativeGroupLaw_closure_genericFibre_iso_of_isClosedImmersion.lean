import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (L : RelativeGroupLaw R f)
    {BK : Scheme.{u}} {gK : BK ⟶ Spec (CommRingCat.of K)} [IsReduced BK] (LBK : RelativeGroupLaw K gK)
    (iK : SchemeHomOver gK (pullback.snd f (specGenericFibreInclusion R K)))
    (hci : IsClosedImmersion iK.1)
    (hiK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t gK),
      NeronModelInfra.schemeHomOverComp (LBK.mul t x y) iK =
        (L.genericFibre K).mul t (NeronModelInfra.schemeHomOverComp x iK) (NeronModelInfra.schemeHomOverComp y iK)) :
    ∃ (LN : RelativeGroupLaw R ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f))
      (e : SchemeHomOver
        (pullback.snd ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) (specGenericFibreInclusion R K)) gK),
      Flat ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LN.mul t x y)
            (⟨(iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι, rfl⟩ :
              SchemeHomOver ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x ⟨(iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨(iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι, rfl⟩)) ∧
      ((∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f)),
        LN.mul t x y = LN.mul t y x) ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t
            (pullback.snd ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LN.genericFibre K).mul t x y) e =
          LBK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e)) ∧
      e.1 ≫ iK.1 =
        pullback.map ((iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι ≫ f) (specGenericFibreInclusion R K)
          f (specGenericFibreInclusion R K) (iK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)).imageι (𝟙 _) (𝟙 _)
          (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp]) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_closure_genericFibre_iso_of_isClosedImmersion.solution
