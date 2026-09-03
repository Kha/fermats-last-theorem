import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_ModularCurve_DRResolvedModelPackage_isFinite_and_finrank_subscheme_comap_comp_eq_natCardV4

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRResolvedModelPackage.isFinite_and_finrank_subscheme_comap_comp_eq_natCardV4
    (p : ℕ) [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ} (R : DRResolvedModelPackage p 𝔛 O κ toκ)
    (v w : X0MqComponents R.width) (hvw : v ≠ w)
    {k : Type} [Field k] (y : (R.comp w).subscheme ⟶ Spec (CommRingCat.of k))
    (hrat : ∀ (n : R.node) (d : Fin (R.width n)),
      (v = DRResolvedModelPackage.chainPos R.width n d ∧ w = DRResolvedModelPackage.chainPos R.width n (d + 1)) ∨
          (w = DRResolvedModelPackage.chainPos R.width n d ∧ v = DRResolvedModelPackage.chainPos R.width n (d + 1)) →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp w).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp w).subschemeι).base) :
    IsFinite (((R.comp v).comap (R.comp w).subschemeι).subschemeι ≫ y) ∧
      ∀ t : Spec (CommRingCat.of k), (((R.comp v).comap (R.comp w).subschemeι).subschemeι ≫ y).finrank t =
        Nat.card {e : Σ n : R.node, Fin (R.width n) //
          (v = DRResolvedModelPackage.chainPos R.width e.1 e.2 ∧ w = DRResolvedModelPackage.chainPos R.width e.1 (e.2 + 1)) ∨
            (w = DRResolvedModelPackage.chainPos R.width e.1 e.2 ∧ v = DRResolvedModelPackage.chainPos R.width e.1 (e.2 + 1))} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRResolvedModelPackage_isFinite_and_finrank_subscheme_comap_comp_eq_natCardV4.solution
