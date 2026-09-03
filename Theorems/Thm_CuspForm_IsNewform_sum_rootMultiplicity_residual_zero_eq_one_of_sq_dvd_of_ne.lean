import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Roots
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_sum_rootMultiplicity_residual_zero_eq_one_of_sq_dvd_of_ne
attribute [-simp] CuspForm.coe_heckeULowerLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

set_option autoImplicit false

open Polynomial IsLocalRing
open scoped TensorProduct IsMulCommutative

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
open scoped Classical in

theorem CuspForm.IsNewform.sum_rootMultiplicity_residual_zero_eq_one_of_sq_dvd_of_ne
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (N : ℕ) [NeZero N] (hN3 : ∀ q : ℕ, q.Prime → ¬ q ^ 3 ∣ N)

    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra Mg 2 (∅ : Set ℕ) →+* ℂ)
    (hchigT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg),
      chig (CuspForm.heckeAlgebra.T hℓ hℓMg (Set.notMem_empty ℓ)) = ModularFormClass.qCoeff g ℓ)
    (hchigU : ∀ (q : ℕ) (hq : q.Prime) (hqMg : q ∣ Mg),
      chig (CuspForm.heckeAlgebra.U hq hqMg (Set.notMem_empty q)) = ModularFormClass.qCoeff g q)
    (ι : chig.range →+* AlgebraicClosure (FractionRing 𝒪))

    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) (hqN : q ^ 2 ∣ N) :
    (let P : Polynomial (AlgebraicClosure (FractionRing 𝒪)) :=
      (if hqP : Nat.Prime q then
        (let aq : AlgebraicClosure (FractionRing 𝒪) := if hqMg : q ∣ Mg
            then ι (chig.rangeRestrict (CuspForm.heckeAlgebra.U hqP hqMg (Set.notMem_empty q)))
            else ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hqP hqMg (Set.notMem_empty q)))
         let e : ℕ := N.factorization q - Mg.factorization q
         if e = 0 then X - C aq
         else X ^ (e - 1) * (X ^ 2 - C aq * X + C (if q ∣ Mg then (0 : AlgebraicClosure (FractionRing 𝒪)) else (q : AlgebraicClosure (FractionRing 𝒪)))))
       else 1)
     ∑ x ∈ P.roots.toFinset,
      if (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
            R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C (0 : ResidueField 𝒪)) ^ R.natDegree)
      then P.rootMultiplicity x else 0) = 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_sum_rootMultiplicity_residual_zero_eq_one_of_sq_dvd_of_ne.solution
