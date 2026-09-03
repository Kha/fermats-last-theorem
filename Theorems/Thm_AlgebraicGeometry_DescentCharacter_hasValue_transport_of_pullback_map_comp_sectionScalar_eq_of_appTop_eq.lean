import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq
    {X Y P X' Y' : Scheme.{u}} {R' : Type u} [CommRing R'] (q : X ⟶ Y)
    (p₁ p₂ : P ⟶ X) (hp : p₁ ≫ q = p₂ ≫ q)
    {N M : Y.Modules} (u : Γ(P, ⊤))
    (σ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M))
    (hσ : ∀ (U : P.Opens) (s : Γ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M), U)),
      σ.app U s = (P.presheaf.map (homOfLE (le_top (a := U))).op u) • s)
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (hβ : (Scheme.Modules.pullback p₁).map β.hom ≫
        (σ ≫ ((Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M by
            rw [hp]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app M)) =
      ((Scheme.Modules.pullbackComp p₁ q).hom.app N ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj N = (Scheme.Modules.pullback (p₂ ≫ q)).obj N by
            rw [hp]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app N) ≫ (Scheme.Modules.pullback p₂).map β.hom)
    (f' : X' ⟶ Spec (CommRingCat.of R')) {T' : X' ⟶ X'} {q' : X' ⟶ Y'} (h' : T' ≫ q' = q') (hT' : T' ≫ f' = f')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (hq : gX ≫ q = q' ≫ gY)
    (s : X' ⟶ P) (hs₁ : s ≫ p₁ = gX) (hs₂ : s ≫ p₂ = T' ≫ gX)
    (c : R') (hsu : s.appTop u = f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv c)) :
    HasValue f' h'
      ((Scheme.Modules.pullbackComp q' gY).app N ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp gX q).app N).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
        (Scheme.Modules.pullbackComp gX q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
        ((Scheme.Modules.pullbackComp q' gY).app M).symm)
      c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.solution
