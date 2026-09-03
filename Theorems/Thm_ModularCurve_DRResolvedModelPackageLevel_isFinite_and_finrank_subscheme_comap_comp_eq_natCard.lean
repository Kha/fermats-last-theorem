import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_ModularCurve_DRResolvedModelPackageLevel_isFinite_and_finrank_subscheme_comap_comp_eq_natCard

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRResolvedModelPackageLevel.isFinite_and_finrank_subscheme_comap_comp_eq_natCard
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀}
    {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (v w : X0MqComponents R.width) (hvw : v ≠ w)
    {k : Type} [Field k] (y : (R.comp w).subscheme ⟶ Spec (CommRingCat.of k))
    (hrat : ∀ (n : R.node) (d : Fin (R.width n)),
      (v = DRResolvedModelPackageLevel.chainPos R.width n d ∧ w = DRResolvedModelPackageLevel.chainPos R.width n (d + 1)) ∨
          (w = DRResolvedModelPackageLevel.chainPos R.width n d ∧ v = DRResolvedModelPackageLevel.chainPos R.width n (d + 1)) →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp w).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp w).subschemeι).base) :
    IsFinite (((R.comp v).comap (R.comp w).subschemeι).subschemeι ≫ y) ∧
      ∀ t : Spec (CommRingCat.of k), (((R.comp v).comap (R.comp w).subschemeι).subschemeι ≫ y).finrank t =
        Nat.card {e : Σ n : R.node, Fin (R.width n) //
          (v = DRResolvedModelPackageLevel.chainPos R.width e.1 e.2 ∧ w = DRResolvedModelPackageLevel.chainPos R.width e.1 (e.2 + 1)) ∨
            (w = DRResolvedModelPackageLevel.chainPos R.width e.1 e.2 ∧ v = DRResolvedModelPackageLevel.chainPos R.width e.1 (e.2 + 1))} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRResolvedModelPackageLevel_isFinite_and_finrank_subscheme_comap_comp_eq_natCard.solution
