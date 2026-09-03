import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle
attribute [-simp] AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.pullback_map_sectionScalar_comp_canonical_unit_and_cocycle
    {X Y P P₃ : Scheme.{u}} (q : X ⟶ Y)
    (p₁ p₂ : P ⟶ X) (hp : p₁ ≫ q = p₂ ≫ q)
    (δ : X ⟶ P) (hδ₁ : δ ≫ p₁ = 𝟙 X) (hδ₂ : δ ≫ p₂ = 𝟙 X)
    (a b : P₃ ⟶ P) (hab : a ≫ p₂ = b ≫ p₁) (c : P₃ ⟶ P) (hca : c ≫ p₁ = a ≫ p₁) (hcb : c ≫ p₂ = b ≫ p₂)
    (M : Y.Modules) (u : Γ(P, ⊤)) (hu₁ : δ.appTop u = 1) (hu₂ : a.appTop u * b.appTop u = c.appTop u)
    (σ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M))
    (hσ : ∀ (U : P.Opens) (s : Γ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M), U)),
      σ.app U s = (P.presheaf.map (homOfLE (le_top (a := U))).op u) • s) :
    let φ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
        (Scheme.Modules.pullback p₂).obj ((Scheme.Modules.pullback q).obj M) :=
      σ ≫ ((Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
        eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M by
          rw [hp]) ≫
        (Scheme.Modules.pullbackComp p₂ q).inv.app M)
    ((Scheme.Modules.pullbackCongr hδ₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp δ p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback δ).map φ ≫
            (Scheme.Modules.pullbackComp δ p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hδ₂).hom.app ((Scheme.Modules.pullback q).obj M) = 𝟙 _) ∧
    (((Scheme.Modules.pullbackComp a p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback a).map φ ≫
          (Scheme.Modules.pullbackComp a p₂).hom.app ((Scheme.Modules.pullback q).obj M)) ≫
      ((Scheme.Modules.pullbackCongr hab).hom.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp b p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback b).map φ ≫
            (Scheme.Modules.pullbackComp b p₂).hom.app ((Scheme.Modules.pullback q).obj M)) =
      (Scheme.Modules.pullbackCongr hca).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullbackComp c p₁).inv.app ((Scheme.Modules.pullback q).obj M) ≫
          (Scheme.Modules.pullback c).map φ ≫
            (Scheme.Modules.pullbackComp c p₂).hom.app ((Scheme.Modules.pullback q).obj M) ≫
              (Scheme.Modules.pullbackCongr hcb).hom.app ((Scheme.Modules.pullback q).obj M)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_pullback_map_sectionScalar_comp_canonical_unit_and_cocycle.solution
