import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of ℤ)} (G : RelativeGroupLaw ℤ f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver t f), G.mul t x y = G.mul t y x)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = G.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : specInt.Fppf} (g : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map g.op s) = GoodReductionJacobian.schemeHomOverComp g.left (MorphismProperty.Over.w g) (e V s))
    (k : ℕ) (n : ℤ) (hkn : (k : ℤ) = n)

    (ρs : 𝒢 ⟶ 𝒢) (φ : SchemeHomOver f f)
    (hφ_sec : ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U (ρs.1.app (op U) s)).1 = (e U s).1 ≫ φ.1)
    (eKm : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f) (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f))
    (heKm_idem : eKm.1 ≫ eKm.1 = eKm.1)
    (heφ : eKm.1 ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φ.1)
    (heKm_hom : ∀ (LK : RelativeGroupLaw ℤ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
      (∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f) f) =
          G.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)) →
      ∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) eKm =
          LK.mul s (NeronModelInfra.schemeHomOverComp x eKm) (NeronModelInfra.schemeHomOverComp y eKm))

    (E : Scheme.{0}) (gX : E ⟶ (Spec (CommRingCat.of ℤ))) (i : E ⟶ A) (j : E ⟶ G.schemeKer k)
    (LE : RelativeGroupLaw ℤ gX)
    (hi : i ≫ f = gX) [IsClosedImmersion i] (hj : j ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = i) [IsClosedImmersion j]
    [IsAffineHom gX] [Flat gX] [LocallyOfFiniteType gX]
    (hfix : ∀ (hj' : j ≫ pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f = gX) {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x : SchemeHomOver s (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)),
      NeronModelInfra.schemeHomOverComp x eKm = x ↔
        ∃ y : SchemeHomOver s gX, NeronModelInfra.schemeHomOverComp y (⟨j, hj'⟩ : SchemeHomOver gX (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ f)) = x)
    (hcommE : ∀ {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t gX), LE.mul t x y = LE.mul t y x)
    (hi_hom : ∀ (hi' : i ≫ f = gX) {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t gX),
      NeronModelInfra.schemeHomOverComp (LE.mul t x y) (⟨i, hi'⟩ : SchemeHomOver gX f) =
        G.mul t (NeronModelInfra.schemeHomOverComp x ⟨i, hi'⟩) (NeronModelInfra.schemeHomOverComp y ⟨i, hi'⟩))
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gX)
    (hePts_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
      ePts T (φ * ψ) = LE.mul _ (ePts T φ) (ePts T ψ))
    (hePts_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
        (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
      (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1)
    (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (sE : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (hsE : ∀ {U V : specInt.Fppf} (g : U ⟶ V) (s : 𝒥.1.obj (op V)) (h : H),
      (Additive.toMul (sE U (𝒥.1.map g.op s))) h = (Scheme.Γ.map g.left.op) ((Additive.toMul (sE V s)) h)) :
    ∃ (ι : 𝒥 ⟶ kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))) (π : kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢)) ⟶ 𝒥)
      (w : (n • 𝟙 𝒢) ≫ ρs = ρs ≫ (n • 𝟙 𝒢)),
      ι ≫ π = 𝟙 𝒥 ∧
      π ≫ ι = kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w ∧
      (∀ (U : specInt.Fppf) (x : 𝒥.1.obj (op U)),
        (e U ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) (ι.1.app (op U) x))).1 =
          U.left.toSpecΓ ≫ (ePts Γ(U.left, ⊤) (Additive.toMul (sE U x))).1 ≫ i) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent.solution
