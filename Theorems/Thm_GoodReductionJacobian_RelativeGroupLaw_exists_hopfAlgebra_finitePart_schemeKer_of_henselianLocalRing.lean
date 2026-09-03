import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
attribute [-simp] NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding exists_isFinite_isOpenImmersion_isClosed_cover_isEmpty_pullback_of_locallyQuasiFinite_of_henselianLocalRing existsUnique_comp_eq_of_universallyClosed_of_closedPoint_notMem_range open NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) [LocallyQuasiFinite (L.schemeKerStr n)] [QuasiCompact (L.schemeKerStr n)] [Flat (L.schemeKerStr n)] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ (j : Spec (CommRingCat.of H) ⟶ L.schemeKer n)
        (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) → L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n),

        j ≫ L.schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap R H)) ∧
        IsOpenImmersion j ∧ IsClosedImmersion j ∧

        (∀ x : ↥(L.schemeKer n), (L.schemeKerStr n).base x = IsLocalRing.closedPoint R → x ∈ Set.range j.base) ∧

        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
          ((e T φ).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ j ≫
              pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T], Function.Injective (e T)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] [Module.Finite R T], Function.Surjective (e T)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing.solution
