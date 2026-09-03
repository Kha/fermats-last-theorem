import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he_add : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = G.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (k : ℕ) (n : ℤ) (hkn : (k : ℤ) = n) :
    ∃ (LK : RelativeGroupLaw R (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f))
      (eK : ∀ U : (Spec (CommRingCat.of R)).Fppf,
        (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U) ≃ SchemeHomOver U.hom (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),

      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
        LK.mul t x y = LK.mul t y x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
        NeronModelInfra.schemeHomOverComp (LK.mul t x y) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
          G.mul t (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)
            (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        Function.Injective (fun y : SchemeHomOver t (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) =>
          NeronModelInfra.schemeHomOverComp y (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f))) ∧

      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
        eK U (s + s') = LK.mul U.hom (eK U s) (eK U s')) ∧
      (∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op V)),
        eK U ((kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.map k.op s) =
          schemeHomOverComp k.left (MorphismProperty.Over.w k) (eK V s)) ∧
      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : (kernel ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.obj (op U)),
        NeronModelInfra.schemeHomOverComp (eK U s) (⟨pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (G.schemeNsmul k) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
          e U ((kernel.ι ((n • 𝟙 𝒢 : 𝒢 ⟶ 𝒢))).1.app (op U) s)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_equiv_obj_kernel_zsmul_schemeHomOver_fst_schemeNsmul.solution
