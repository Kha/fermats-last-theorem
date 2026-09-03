import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient
    {X : Scheme.{u}} (R : Type u) [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] [Algebra R k]
    (η : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k))))) :
    letI : Algebra R (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η)) :=
      RingHom.toAlgebra ((X.presheaf.germ ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η) trivial).hom.comp
        ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))
    letI : Algebra k ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).residueField η) :=
      RingHom.toAlgebra (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).residue η).hom.comp
        (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).presheaf.germ ⊤ η trivial).hom.comp
          (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).appTop).hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)))
    ∃ (𝔮 : Ideal (k ⊗[R] (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η)))) (_ : 𝔮.IsPrime)
      (ψ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).residueField η ≃ₐ[k] FractionRing ((k ⊗[R] (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η))) ⧸ 𝔮)),
      (∀ s : (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η)),
        ψ (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).residue η).hom
            (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).stalkMap η).hom s)) =
          (Localization.mk (Ideal.Quotient.mk 𝔮 ((1 : k) ⊗ₜ[R] s)) 1 : FractionRing ((k ⊗[R] (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η))) ⧸ 𝔮))) ∧
      ((∀ η' : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R k)))), η' ⤳ η → η' = η) → 𝔮 ∈ minimalPrimes (k ⊗[R] (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R k)))).base η)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient.solution
