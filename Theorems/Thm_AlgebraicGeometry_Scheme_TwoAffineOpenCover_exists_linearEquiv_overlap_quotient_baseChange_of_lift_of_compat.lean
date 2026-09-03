import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover)
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B)
    (M : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (J0 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A0)
    (J1 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A1)
    (J01 : Ideal ((𝒱.pullback c B).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B))).A01) :
    let 𝒱B := 𝒱.pullback c B
    let cB := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B)
    let 𝒱BI := 𝒱.pullback c (B ⧸ I)
    let cBI := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))
    let A0B := (𝒱B.cover cB).A0
    let A1B := (𝒱B.cover cB).A1
    let A01B := (𝒱B.cover cB).A01
    let P0 := (𝒱BI.sectionsOf cBI M).M0
    let P1 := (𝒱BI.sectionsOf cBI M).M1
    ∀ (φ0 : A0B ⧸ J0 ≃+* (𝒱BI.cover cBI).A0)
      (φ1 : A1B ⧸ J1 ≃+* (𝒱BI.cover cBI).A1)
      (φ01 : A01B ⧸ J01 ≃+* (𝒱BI.cover cBI).A01)
      (_ : ∀ a, φ01 (Ideal.Quotient.mk J01 ((𝒱B.cover cB).ρ0 a)) =
                (𝒱BI.cover cBI).ρ0 (φ0 (Ideal.Quotient.mk J0 a)))
      (_ : ∀ a, φ01 (Ideal.Quotient.mk J01 ((𝒱B.cover cB).ρ1 a)) =
                (𝒱BI.cover cBI).ρ1 (φ1 (Ideal.Quotient.mk J1 a)))
      (P0' : Type u) [AddCommGroup P0'] [Module A0B P0'] [Module.Projective A0B P0']
      (P1' : Type u) [AddCommGroup P1'] [Module A1B P1'] [Module.Projective A1B P1'],
      letI : Module (A0B ⧸ J0) P0 := Module.compHom P0 φ0.toRingHom
      letI : Module (A1B ⧸ J1) P1 := Module.compHom P1 φ1.toRingHom
      ∀ (iso0 : (A0B ⧸ J0) ⊗[A0B] P0' ≃ₗ[A0B ⧸ J0] P0)
        (iso1 : (A1B ⧸ J1) ⊗[A1B] P1' ≃ₗ[A1B ⧸ J1] P1),
      letI : Algebra A0B A01B := (𝒱B.cover cB).ρ0.toRingHom.toAlgebra
      letI : Algebra A1B A01B := (𝒱B.cover cB).ρ1.toRingHom.toAlgebra
      letI : Module (A01B ⧸ J01) (𝒱BI.sectionsOf cBI M).M01 := Module.compHom _ φ01.toRingHom
      ∃ (iso01₀ : (A01B ⧸ J01) ⊗[A01B] (A01B ⊗[A0B] P0') ≃ₗ[A01B ⧸ J01] (𝒱BI.sectionsOf cBI M).M01)
        (iso01₁ : (A01B ⧸ J01) ⊗[A01B] (A01B ⊗[A1B] P1') ≃ₗ[A01B ⧸ J01] (𝒱BI.sectionsOf cBI M).M01),
        (∀ p : P0', iso01₀ ((1 : A01B ⧸ J01) ⊗ₜ[A01B] ((1 : A01B) ⊗ₜ[A0B] p)) =
              (𝒱BI.sectionsOf cBI M).r0 (iso0 ((1 : A0B ⧸ J0) ⊗ₜ[A0B] p))) ∧
        (∀ p : P1', iso01₁ ((1 : A01B ⧸ J01) ⊗ₜ[A01B] ((1 : A01B) ⊗ₜ[A1B] p)) =
              (𝒱BI.sectionsOf cBI M).r1 (iso1 ((1 : A1B ⧸ J1) ⊗ₜ[A1B] p))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat.solution
