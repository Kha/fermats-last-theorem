import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
    {k : Type u} [Field k]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {C : Scheme.{u}} (ι : C ⟶ A) [IsClosedImmersion ι] [IsFinite (ι ≫ f)]
    (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)), ∃ P₀ : T ⟶ C, P₀ ≫ ι = (L.one t).1)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      (∃ P₀ : T ⟶ C, P₀ ≫ ι = P.1) → (∃ Q₀ : T ⟶ C, Q₀ ≫ ι = Q.1) →
        (∃ R₀ : T ⟶ C, R₀ ≫ ι = (L.mul t P Q).1) ∧ (∃ S₀ : T ⟶ C, S₀ ≫ ι = (L.inv t P).1)) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra k H),
      Module.Finite k H ∧ Coalgebra.IsCocomm k H ∧
      ∃ (j : Spec (CommRingCat.of H) ⟶ C)
        (e : ∀ (T : Type u) [CommRing T] [Algebra k T],
          WithConv (H →ₐ[k] T) →
            {P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k T))) f // ∃ P₀ : _ ⟶ C, P₀ ≫ ι = P.1}),
        IsIso j ∧

        j ≫ ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k H)) ∧

        (∀ (T : Type u) [CommRing T] [Algebra k T] (φ : WithConv (H →ₐ[k] T)),
          ((e T φ).val : SchemeHomOver _ f).1 = Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ j ≫ ι) ∧
        (∀ (T : Type u) [CommRing T] [Algebra k T], Function.Bijective (e T)) ∧

        (∀ (T : Type u) [CommRing T] [Algebra k T] (φ ψ : WithConv (H →ₐ[k] T)),
          ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val) ∧

        (∀ (T T' : Type u) [CommRing T] [Algebra k T] [CommRing T'] [Algebra k T']
            (g : T →ₐ[k] T') (φ : WithConv (H →ₐ[k] T)),
          ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup.solution
