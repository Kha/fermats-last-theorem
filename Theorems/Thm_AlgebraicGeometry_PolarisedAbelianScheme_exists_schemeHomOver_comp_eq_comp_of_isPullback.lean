import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_schemeHomOver_comp_eq_comp_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOver_comp_eq_comp_of_isPullback
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
    (gA : u'.A ⟶ u.A) (hg : CategoryTheory.IsPullback gA u'.f u.f (Spec.map (CommRingCat.ofHom φ)))
    (hgmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ gA =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hgpol : Nonempty ((Scheme.Modules.pullback gA).obj u.pol ≅ u'.pol))
    (σ : SchemeHomOver u.f u.f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t u.f),
      NeronModelInfra.schemeHomOverComp (u.L.mul t x y) σ =
        u.L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj u.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol)) :
    ∃ σ' : SchemeHomOver u'.f u'.f, IsIso σ'.1 ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t u'.f),
        NeronModelInfra.schemeHomOverComp (u'.L.mul t x y) σ' =
          u'.L.mul t (NeronModelInfra.schemeHomOverComp x σ') (NeronModelInfra.schemeHomOverComp y σ')) ∧
      (∀ s : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (u'.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ'.1).obj u'.pol) ≅
          (Scheme.Modules.pullback (u'.f ⁻¹ᵁ U).ι).obj u'.pol)) ∧
      σ'.1 ≫ gA = gA ≫ σ.1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_schemeHomOver_comp_eq_comp_of_isPullback.solution
