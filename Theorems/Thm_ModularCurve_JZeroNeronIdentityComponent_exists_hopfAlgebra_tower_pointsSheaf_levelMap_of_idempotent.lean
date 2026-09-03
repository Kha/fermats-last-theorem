import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
set_option Elab.async false
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.JZeroNeronIdentityComponent.exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hqp : q ≠ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (N : JZeroNeronIdentityComponent p)

    (hAff : ∀ m, IsAffineHom (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)) (hFlat : ∀ m, Flat (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g))
    (hLft : ∀ m, LocallyOfFiniteType (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)) (hSep : ∀ m, IsSeparated (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g))

    (t : letI := heckeModuleBar p; ℕ → HeckeAlg) (φt : ℕ → SchemeHomOver N.g N.g)
    (eK : ∀ m, SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g))
    (ht : letI := heckeModuleBar p
      ∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 → (t m • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m))
    (heK_idem : ∀ m, (eK m).1 ≫ (eK m).1 = (eK m).1)
    (hφt_pts : letI := heckeModuleBar p; ∀ (m : ℕ) (x : JZero p), (N.pts (t m • x)).1 = (N.pts x).1 ≫ (φt m).1)
    (heφ : ∀ m, (eK m).1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φt m).1)
    (hlevel : ∀ m, pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φt (m + 1)).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φt m).1)
    (heK_hom : ∀ (m : ℕ) (LK : RelativeGroupLaw ℤ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
      (∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) N.g) =
          N.L.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)) →
      ∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (eK m) =
          LK.mul s (NeronModelInfra.schemeHomOverComp x (eK m)) (NeronModelInfra.schemeHomOverComp y (eK m))) :
    ∃ (H : ℕ → Type) (_ : ∀ m, CommRing (H m)) (_ : ∀ m, HopfAlgebra ℤ (H m))
      (E : ℕ → Scheme.{0}) (gX : ∀ m, E m ⟶ (Spec (CommRingCat.of ℤ))) (i : ∀ m, E m ⟶ N.G) (j : ∀ m, E m ⟶ N.L.schemeKer (q ^ m))
      (LE : ∀ m, RelativeGroupLaw ℤ (gX m))
      (ePts : ∀ (m : ℕ) (T : Type) [CommRing T] [Algebra ℤ T],
        WithConv (H m →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) (gX m))
      (genericPoints : ∀ m, WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ)) ≃ ↥(eisensteinPrimaryTorsionBar p q m))
      (pFibrePoints : ∀ m, WithConv (H m →ₐ[ℤ] ↥A) ≃ ↥(toricEisensteinPrimaryPart p q A hA m))
      (𝒥 : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1})
      (sE : ∀ (m : ℕ) (U : specInt.Fppf), (𝒥 m).1.obj (op U) ≃+ Additive (WithConv (H m →ₐ[ℤ] Γ(U.left, ⊤))))
      (levelMap : ∀ m, H (m + 1) →ₐc[ℤ] H m)
      (incl : ∀ m, 𝒥 m ⟶ 𝒥 (m + 1)) (Q : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1})
      (proj : ∀ m, 𝒥 (m + 1) ⟶ Q m) (incl_proj : ∀ m, incl m ≫ proj m = 0),

      (∀ m, Algebra.FiniteType ℤ (H m)) ∧ (∀ m, Module.Flat ℤ (H m)) ∧
      (∀ (m ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
        Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) (H m))) ∧

      (∀ m, i m ≫ N.g = gX m) ∧ (∀ m, IsClosedImmersion (i m)) ∧
      (∀ m, j m ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = i m) ∧ (∀ m, IsClosedImmersion (j m)) ∧

      (∀ m (hj : j m ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g = gX m) {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
        NeronModelInfra.schemeHomOverComp x (eK m) = x ↔
          ∃ y : SchemeHomOver s (gX m), NeronModelInfra.schemeHomOverComp y (⟨j m, hj⟩ : SchemeHomOver (gX m) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)) = x) ∧
      (∀ m, IsAffineHom (gX m)) ∧ (∀ m, Flat (gX m)) ∧ (∀ m, LocallyOfFiniteType (gX m)) ∧
      (∀ m {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t (gX m)), (LE m).mul t x y = (LE m).mul t y x) ∧
      (∀ m (hi : i m ≫ N.g = gX m) {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t (gX m)),
        NeronModelInfra.schemeHomOverComp ((LE m).mul t x y) (⟨i m, hi⟩ : SchemeHomOver (gX m) N.g) =
          N.L.mul t (NeronModelInfra.schemeHomOverComp x ⟨i m, hi⟩) (NeronModelInfra.schemeHomOverComp y ⟨i m, hi⟩)) ∧
      (∀ m (x : JZero p), x ∈ eisensteinPrimaryTorsionBar p q m ↔
        ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) (gX m), y.1 ≫ i m = (N.pts x).1) ∧
      (∀ (m : ℕ) (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H m →ₐ[ℤ] T)),
        ePts m T (φ * ψ) = (LE m).mul _ (ePts m T φ) (ePts m T ψ)) ∧
      (∀ (m : ℕ) (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
          (σ : T →ₐ[ℤ] T') (φ : WithConv (H m →ₐ[ℤ] T)),
        (ePts m T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts m T φ).1) ∧
      (∀ (m : ℕ) (T : Type) [CommRing T] (f g : WithConv (H m →ₐ[ℤ] T)), f * g = g * f) ∧

      (∀ m (φ : WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ))),
        (N.pts ((genericPoints m φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)).1 = (ePts m (AlgebraicClosure ℚ) φ).1 ≫ i m) ∧
      (∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ)), genericPoints m (f * g) = genericPoints m f + genericPoints m g) ∧
      (∀ m, ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ f g : WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ)), (∀ h : H m, g h = σ (f h)) →
        ((genericPoints m g : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
          = σ • ((genericPoints m f : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) ∧

      (∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] ↥A), pFibrePoints m (f * g) = pFibrePoints m f + pFibrePoints m g) ∧
      (∀ m, ∀ φ : WithConv (H m →ₐ[ℤ] ↥A), ∀ ψ : WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ)), (∀ h : H m, ψ h = A.subtype (φ h)) →
        ((pFibrePoints m φ : ↥(toricEisensteinPrimaryPart p q A hA m)) : JZero p)
          = ((genericPoints m ψ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) ∧

      (∀ (m : ℕ) {U V : specInt.Fppf} (f : U ⟶ V) (s : (𝒥 m).1.obj (op V)) (h : H m),
        (Additive.toMul (sE m U ((𝒥 m).1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (sE m V s)) h)) ∧
      (∀ m, Function.Surjective (levelMap m)) ∧
      (∀ m (φ : WithConv (H m →ₐ[ℤ] (AlgebraicClosure ℚ))),
        ((genericPoints (m + 1) (WithConv.toConv ((WithConv.ofConv φ).comp (levelMap m : H (m + 1) →ₐ[ℤ] H m)))
            : ↥(eisensteinPrimaryTorsionBar p q (m + 1))) : JZero p)
          = ((genericPoints m φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) ∧
      (∀ (m : ℕ) (U : specInt.Fppf) (s : (𝒥 m).1.obj (op U)) (h' : H (m + 1)),
        (Additive.toMul (sE (m + 1) U ((incl m).hom.app (op U) s))) h' = (Additive.toMul (sE m U s)) (levelMap m h')) ∧
      (∀ m, Mono (incl m)) ∧
      (∀ m, (ShortComplex.mk (incl m) (proj m) (incl_proj m)).ShortExact) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_hopfAlgebra_tower_pointsSheaf_levelMap_of_idempotent.solution
