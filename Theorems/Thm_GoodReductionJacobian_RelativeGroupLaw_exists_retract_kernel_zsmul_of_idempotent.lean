import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_of_idempotent

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_of_idempotent
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he_add : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = G.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (j : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map j.op s) = schemeHomOverComp j.left (MorphismProperty.Over.w j) (e V s))

    (k : ℕ) (n : ℤ) (hkn : (k : ℤ) = n)
    (LK : RelativeGroupLaw R (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))
    (hLK_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
      NeronModelInfra.schemeHomOverComp (LK.mul t x y) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
        G.mul t (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)
          (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩))
    (hLK_inj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      Function.Injective (fun y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) =>
        NeronModelInfra.schemeHomOverComp y (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f)))
    (eK : ∀ U : (Spec (CommRingCat.of R)).Fppf, (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U) ≃ SchemeHomOver U.hom (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))
    (heK_add : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
      eK U (s + s') = LK.mul U.hom (eK U s) (eK U s'))
    (heK : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (j : U ⟶ V) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op V)),
      eK U ((kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.map j.op s) = schemeHomOverComp j.left (MorphismProperty.Over.w j) (eK V s))

    (ρs : 𝒢 ⟶ 𝒢) (w : (n • 𝟙 𝒢) ≫ ρs = ρs ≫ (n • 𝟙 𝒢))
    (eKm : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))
    (heKm_idem : eKm.1 ≫ eKm.1 = eKm.1)
    (heKm_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
      NeronModelInfra.schemeHomOverComp (LK.mul t x y) eKm =
        LK.mul t (NeronModelInfra.schemeHomOverComp x eKm) (NeronModelInfra.schemeHomOverComp y eKm))
    (hρs : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
      eK U ((kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w).1.app (op U) s) = NeronModelInfra.schemeHomOverComp (eK U s) eKm)

    (E : Scheme.{u}) (i : E ⟶ pullback (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1)
    [IsClosedImmersion i]
    (LE : RelativeGroupLaw R (i ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)))
    (hLE_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (i ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))),
      NeronModelInfra.schemeHomOverComp (LE.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)) (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)) =
        LK.mul t (NeronModelInfra.schemeHomOverComp x ⟨i, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩))
    (hfix : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
      NeronModelInfra.schemeHomOverComp x eKm = x ↔
        ∃ y : SchemeHomOver t (i ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)), NeronModelInfra.schemeHomOverComp y ⟨i, rfl⟩ = x)
    (𝒢E : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (eE : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢E.1.obj (op U) ≃ SchemeHomOver U.hom (i ≫ (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)))
    (heE_add : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢E.1.obj (op U)), eE U (s + s') = LE.mul U.hom (eE U s) (eE U s'))
    (heE : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (j : U ⟶ V) (s : 𝒢E.1.obj (op V)),
        eE U (𝒢E.1.map j.op s) = schemeHomOverComp j.left (MorphismProperty.Over.w j) (eE V s)) :
    ∃ (ι : 𝒢E ⟶ kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))) (π : kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢)) ⟶ 𝒢E),
      ι ≫ π = 𝟙 𝒢E ∧
      π ≫ ι = kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) ρs ρs w ∧
      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (x : 𝒢E.1.obj (op U)),
        eK U (ι.1.app (op U) x) = NeronModelInfra.schemeHomOverComp (eE U x) ⟨i, rfl⟩) ∧
      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
        NeronModelInfra.schemeHomOverComp (eE U (π.1.app (op U) s)) ⟨i, rfl⟩ =
          NeronModelInfra.schemeHomOverComp (eK U s) eKm) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_of_idempotent.solution
