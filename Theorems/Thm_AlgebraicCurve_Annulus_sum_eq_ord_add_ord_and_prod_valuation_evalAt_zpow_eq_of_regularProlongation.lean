import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
    {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
    (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0)

    (Ra : RegularProlongation A F Fa) (xa : Place (ResidueField A) Fa)
    (hza : An.param ∈ Ra.integers) (hxa : xa.ord (Ra.residue ⟨An.param, hza⟩) = 1)
    (hslope_a : ∀ (f : F) (hf : f ∈ Ra.integers), Ra.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(xa.ord (Ra.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))

    (Rb : RegularProlongation A F Fb) (xb : Place (ResidueField A) Fb)
    (hzb : algebraMap L F (An.modulus : L) * An.param⁻¹ ∈ Rb.integers)
    (hxb : xb.ord (Rb.residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb⟩) = 1)
    (hslope_b : ∀ (f : F) (hf : f ∈ Rb.integers), Rb.residue ⟨f, hf⟩ ≠ 0 →
      (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
        ∃ h : P.evalAt f * (P.evalAt (algebraMap L F (An.modulus : L) * An.param⁻¹)) ^
          (-(xb.ord (Rb.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A))

    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param))

    (h : F) (hh0 : h ≠ 0) (hha : h ∈ Ra.integers) (hresa : Ra.residue ⟨h, hha⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0)
    (hhb : (algebraMap L F c')⁻¹ * h ∈ Rb.integers) (hresb : Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ ≠ 0)

    (D : Divisor L F) (hDsupp : ∀ P ∈ D.support, P ∈ An.dom) (hD : ∀ P ∈ An.dom, D P = P.ord h) :
    (D.sum fun _ n => n) = xa.ord (Ra.residue ⟨h, hha⟩) + xb.ord (Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩) ∧
    (D.prod fun P n => A.valuation (P.evalAt An.param) ^ n) =
      A.valuation c' * A.valuation (An.modulus : L) ^ (xb.ord (Rb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation.solution
