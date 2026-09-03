import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_exists_opens_preimage_eq_of_isClosedMap_of_saturated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.exists_opens_preimage_eq_of_isClosedMap_of_saturated
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (X₁ : Scheme.{u}) (π : M.X ⟶ X₁)
    (hcl : IsClosedMap π.base) (hsurj : Function.Surjective π.base)
    (hfib_sp : ∀ x x' : M.X, π.base x' = π.base x → M.toBase.base x = IsLocalRing.closedPoint ↥A → x' = x)
    (hfib_gen : ∀ x' : M.X, π.base x' = π.base (genericPoint M.X) → x' = genericPoint M.X)
    (hfib_pt : ∀ (P : Place L F) (x' : M.X), π.base x' = π.base (M.pt P) → ∃ P' : Place L F, x' = M.pt P')
    (G : Place L F → ℤ)
    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F) (hU : (⨆ a, U a) = ⊤)
    (hv2 : ∀ a, (∀ P : Place L F, M.pt P ∈ U a ↔ G P = 0) ∨
        (∃ (i : ιV) (q : Place (IsLocalRing.ResidueField A) (Fbar i)), ∀ P : Place L F,
          M.pt P ∈ U a ↔ ((P ∈ (C i).dom ∧ (C i).placeMap P = q) ∨ (G P = 0 ∧ P.ord (h a) = 0))) ∨
        (∃ e₀ : ιE, ∀ P : Place L F,
          M.pt P ∈ U a ↔ (P ∈ (An e₀).dom ∨ (G P = 0 ∧ P.ord (h a) = 0))))
    (hGfib : ∀ P P' : Place L F, π.base (M.pt P) = π.base (M.pt P') → (G P = 0 ↔ G P' = 0))
    (hhfib : ∀ a (P P' : Place L F), π.base (M.pt P) = π.base (M.pt P') →
      (P.ord (h a) = 0 ↔ P'.ord (h a) = 0)) :
    ∃ U₁ : Fin r → X₁.Opens, (⨆ a, U₁ a) = ⊤ ∧ ∀ a (x : M.X), x ∈ U a ↔ π.base x ∈ U₁ a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_exists_opens_preimage_eq_of_isClosedMap_of_saturated.solution
