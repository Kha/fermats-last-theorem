import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq
import P2M.Util
import P2M.Sol.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem V3Glue.ChartInput.exists_iso_geometricFibre_strictTransform
    {X : Scheme.{0}} {N : Type} (C : V3Glue.ChartInput X N)
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0) (j : Fin 2)

    {R Xκ Bκ : Scheme.{0}} (c : R ⟶ Xκ) [IsClosedImmersion c] [IsIntegral R]
    (bcm : Xκ ⟶ X) (p₂ : Xκ ⟶ Bκ) (b : Bκ ⟶ C.B) (hP : IsPullback bcm p₂ C.πX b)
    (hξj : ξ j = (c ≫ bcm).base (genericPoint R))
    (hdesc : bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) = Set.range c.base)
    {pt : C.B} (hpt : IsClosed ({pt} : Set C.B)) (hfib : Set.range bcm.base = C.πX.base ⁻¹' {pt})
    (hcpt : ∀ r : R, (c ≫ bcm ≫ C.πX).base r = pt)

    {F : N → Scheme.{0}} (lam : ∀ n, F n ⟶ C.Res n) [∀ n, IsClosedImmersion (lam n)]
    [∀ n, IsClosedImmersion (lam n ≫ C.ρ n)] [∀ n, IsReduced (pullback (C.g n) (lam n))]
    (horient_fwd : ∀ n (y : C.U n), (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base →
      (y : X) ∈ Set.range (c ≫ bcm).base)
    (horient_conv : ∀ n (y : C.U n), (y : X) ∈ Set.range (c ≫ bcm).base →
      (C.f n).base y ∈ Set.range (lam n ≫ C.ρ n).base)
    (hxim : ∀ n, C.x n ∈ Set.range (c ≫ bcm).base)

    (n₀ : N) {B₀ : Scheme.{0}} (i : B₀ ⟶ C.B) [Mono i] (a : Bκ ⟶ B₀) [Flat a] (hb : b = a ≫ i)
    (s₀ : (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subscheme ⟶ B₀)
    (hsB : (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX = s₀ ≫ i)
    (hGκ : IsReduced (pullback (pullback.fst (C.g n₀) (lam n₀) ≫ C.toB n₀) b)) :
    ∃ e : pullback ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR ≫ C.πX) b ⟶ R,
      IsIso e ∧ e ≫ c ≫ p₂ = pullback.snd _ _ ∧
        e ≫ c ≫ bcm = pullback.fst _ _ ≫ (C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).subschemeι ≫ C.toGlueInput.toDR := by p2m_exact_reverting @_root_.P2MW.S_V3Glue_ChartInput_exists_iso_geometricFibre_strictTransform.solution
