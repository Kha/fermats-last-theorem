import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne

set_option autoImplicit false

open AlgebraicCurve

theorem
    AlgebraicCurve.Annulus.exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar : Type} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (An₁ An₂ : Annulus A F) (hdom : An₂.dom = An₁.dom)
    (C : ComponentChart A F Fbar) (x : Place (IsLocalRing.ResidueField A) Fbar) (hx : x.IsRational)
    (hatt : An₁.IsAttached C x)
    (hz₂ : ∃ h : An₂.param ∈ C.integers, C.residue ⟨An₂.param, h⟩ ≠ 0) :
    ∃ r : IsLocalRing.ResidueField A, r ≠ 0 ∧
      ∀ P ∈ An₁.dom, ∃ h : P.evalAt An₂.param * (P.evalAt An₁.param)⁻¹ ∈ A,
        IsUnit (⟨_, h⟩ : A) ∧ IsLocalRing.residue A ⟨_, h⟩ = r := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_exists_forall_isUnit_evalAt_param_mul_inv_residue_eq_of_dom_eq_of_isAttached_of_rankOne.solution
