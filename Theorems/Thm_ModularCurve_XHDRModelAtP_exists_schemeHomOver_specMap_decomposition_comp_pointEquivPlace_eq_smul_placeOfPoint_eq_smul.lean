import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (frob : SemilinearAut (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)))
    (hfrob : ∀ (x : ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM))) (n : ℤ),
      ((frob • x : ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM))) :
          LaurentSeries (ResidueField ↥A)).coeff n =
        ((x : LaurentSeries (ResidueField ↥A)).coeff n) ^ p)

    (hN : (p : Γ((fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), ⊤)) = 0)
    (θN : (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶ (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hθN₁ : θN ≫ pullback.fst _ _ = (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).frobenius p 1 Fact.out hN ≫ pullback.fst _ _)
    (hθN₂ : θN ≫ pullback.snd _ _ = pullback.snd _ _)

    (hM : (p : Γ((fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), ⊤)) = 0)
    (θM : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hθM₁ : θM ≫ pullback.fst _ _ = (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).frobenius p 1 Fact.out hM ≫ pullback.fst _ _)
    (hθM₂ : θM ≫ pullback.snd _ _ = pullback.snd _ _)

    (hfrobpl : ∀ P : closedPoints (𝔛.Mfib A hA ρ hρ).C,
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base ((𝔛.efib A hA ρ hρ ≫ θN).base P.1) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ = frob • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)

    (Fr : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hFr : Fr ∈ A.decompositionSubgroup ℚ)
    (φκ : ResidueField ↥A →+* ResidueField ↥A) (hφκ : ∀ a : ResidueField ↥A, φκ a = a ^ p)
    (hFrφ : ∀ a : ↥A, IsLocalRing.residue ↥A ((⟨Fr, hFr⟩ : ↥(A.decompositionSubgroup ℚ)) • a) = φκ (IsLocalRing.residue ↥A a))

    (i : Fin 2)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))

    (hcompP : (𝔛.comp A hA ρ hρ i).base (θN.base ((𝔛.efib A hA ρ hρ).base P.1)) =
      θM.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1)) :
    ∃ (y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ u'.1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧
      u'.1 = Spec.map (CommRingCat.ofHom
        (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) (↥A) ⟨Fr, hFr⟩)) ≫ u.1 ∧
      Set.range u'.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) ∧
      𝔛.Meta.pointEquivPlace y' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) Fr • 𝔛.Meta.pointEquivPlace y ∧
      ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        uκ' = uκ ≫ θM ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          (𝔛.Mfib A hA ρ hρ).placeOfPoint P' = frob • (𝔛.Mfib A hA ρ hρ).placeOfPoint P := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_specMap_decomposition_comp_pointEquivPlace_eq_smul_placeOfPoint_eq_smul.solution
