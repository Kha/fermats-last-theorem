import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne
attribute [-simp] CuspForm.coe_heckeULowerLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

open Polynomial IsLocalRing

theorem CuspForm.IsNewform.qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (Mg : ℕ) [NeZero Mg]
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg),
      chig (CuspForm.heckeAlgebra.T hℓ hℓMg (Set.notMem_empty ℓ)) = ModularFormClass.qCoeff g ℓ)
    (iota : chig.range →+* AlgebraicClosure (FractionRing 𝒪))

    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    (q ^ 2 ∣ Mg → ModularFormClass.qCoeff g q = 0) ∧
    (q ∣ Mg → ¬ q ^ 2 ∣ Mg → ∃ a : ℤ, (a = 1 ∨ a = -1) ∧ ModularFormClass.qCoeff g q = (a : ℂ)) ∧
    (∀ hqMg : ¬ q ∣ Mg,
      ∀ x ∈ (X ^ 2 - C (iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hq hqMg (Set.notMem_empty q)))) * X
              + C ((q : ℕ) : AlgebraicClosure (FractionRing 𝒪))).roots,
        ¬ (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
          R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (0 : ResidueField 𝒪)) ^ R.natDegree)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_qCoeff_eq_zero_and_sq_eq_one_and_not_residual_zero_of_mem_roots_of_ne.solution
