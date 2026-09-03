import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_comp_specMap_quotient_maximalIdeal_pow_eq_of_section_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_comp_specMap_quotient_maximalIdeal_pow_eq_of_section_comp_eq
    {k : Type u} [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    (P₀ : Spec (CommRingCat.of k) ⟶ P) (hP₀ : P₀ ≫ p = 𝟙 _) (n : ℕ)
    (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k)) ⧸
        IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k))) ^ n)) ⟶ P)
    (hjn : jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P.fromSpecStalk _)
    (g : Spec (CommRingCat.of (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k)) ⧸
        IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k))) ^ n)) ⟶
        Spec (CommRingCat.of k))
    (hg : jn ≫ p = g)
    (σ : Spec (CommRingCat.of k) ⟶
      Spec (CommRingCat.of (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k)) ⧸
        IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k))) ^ n)))
    (hσ : σ ≫ jn = P₀)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) [CompactSpace ↥Y] [QuasiSeparatedSpace ↥Y]
    (ι : Y ⟶ pullback y g) (hι₁ : ι ≫ pullback.fst y g = 𝟙 Y)
    (hι₂ : ι ≫ pullback.snd y g = y ≫ σ)
    (α : pullback y g ⟶ P) (hα : ι ≫ α = y ≫ P₀) :
    ∃ β : pullback y g ⟶
        Spec (CommRingCat.of (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k)) ⧸
          IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.base (IsLocalRing.closedPoint k))) ^ n)),
      β ≫ jn = α := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_comp_specMap_quotient_maximalIdeal_pow_eq_of_section_comp_eq.solution
