import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_monoidHom_semilinearAut_reduction_smul_eq_of_smoothOfRelativeDimension_one_fixedBase

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve

theorem AlgebraicCurve.exists_monoidHom_semilinearAut_reduction_smul_eq_of_smoothOfRelativeDimension_one_fixedBase
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (R₀ : Type) [CommRing R₀] (i : R₀ →+* ↥O)
    (hi : ∀ s : ↥(O.decompositionSubgroup ℚ),
      (MulSemiringAction.toRingHom (↥(O.decompositionSubgroup ℚ)) ↥O s).comp i = i)
    (X₁ : Scheme.{0}) (π₁ : X₁ ⟶ Spec (CommRingCat.of R₀)) [IsProper π₁] [SmoothOfRelativeDimension 1 π₁]

    (F : Type) [Field F] [Algebra (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i)))) [IsIso e]
    (he : e ≫ pullback.snd π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i))) = 𝔐.toBase)

    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) F)
    (hgal_base : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      SemilinearAut.baseAut (gal σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (hgal_pts : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x y : {x₀ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔐.C // x₀ ≫ 𝔐.toBase = 𝟙 _},
        y.1 ≫ e ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i))) =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ e ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i))) →
        𝔐.pointEquivPlace y = gal σ • 𝔐.pointEquivPlace x)

    (K : Type) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π₁ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π₁ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i))) = 𝔐k.toBase)

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hlift : ∀ P : Place (AlgebraicClosure ℚ) F, ∃ Pt : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) π₁,
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i)))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (Spec.map (CommRingCat.ofHom i)) π₁),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom (O.subtype.comp i)))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫
          pullback.fst π₁ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1) :
    ∃ galk : ↥(O.decompositionSubgroup ℚ) →* SemilinearAut (IsLocalRing.ResidueField ↥O) K,

      (∀ s : ↥(O.decompositionSubgroup ℚ), SemilinearAut.baseAut (galk s) =
          MulSemiringAction.toRingAut (↥(O.decompositionSubgroup ℚ)) (IsLocalRing.ResidueField ↥O) s) ∧

      (∀ (s : ↥(O.decompositionSubgroup ℚ))
        (x y : {x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥O)) ⟶ 𝔐k.C // x₀ ≫ 𝔐k.toBase = 𝟙 _}),
        y.1 ≫ ek ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i))) =
          Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (↥(O.decompositionSubgroup ℚ))
              (IsLocalRing.ResidueField ↥O) s)) ≫
            x.1 ≫ ek ≫ pullback.fst π₁ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥O).comp i))) →
        𝔐k.pointEquivPlace y = galk s • 𝔐k.pointEquivPlace x) ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ O.decompositionSubgroup ℚ)
        (P : Place (AlgebraicClosure ℚ) F),
        red (gal σ • P) = galk ⟨σ, hσ⟩ • red P) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_monoidHom_semilinearAut_reduction_smul_eq_of_smoothOfRelativeDimension_one_fixedBase.solution
