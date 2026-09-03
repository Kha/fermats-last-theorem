import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_spec_schemeKer_of_forall_equiv_torsionSubset

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_iso_spec_schemeKer_of_forall_equiv_torsionSubset
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) [IsAffineHom (L.schemeKerStr n)]
    (H : Type u) [CommRing H] [Algebra R H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra R T],
      WithConv (H →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (a : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
      ((e T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e T φ).val.1) :
    ∃ i : Spec (CommRingCat.of H) ≅ L.schemeKer n,
      i.hom ≫ L.schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap R H)) ∧
      ∀ (T : Type u) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
        ((e T φ).val : SchemeHomOver _ f).1 =
          Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ i.hom ≫
            pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_spec_schemeKer_of_forall_equiv_torsionSubset.solution
