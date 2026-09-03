import Mathlib
import Definitions.Def_MvFormalGroup_FirstOrderDeformation
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_MvFormalGroup_mem_firstOrderCoboundaries_iff
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

set_option autoImplicit false

open MvPowerSeries MvFormalGroup
theorem MvFormalGroup.mem_firstOrderCoboundaries_iff
    {k : Type} [Field k] {d : ℕ} (G₀ : MvFormalGroup d k) [G₀.IsComm]
    (b : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :
    b ∈ firstOrderCoboundaries G₀ ↔
      ∃ η : Fin d → MvPowerSeries (Fin d) k, (∀ i, constantCoeff (η i) = 0) ∧
        ∀ l, b l = ∑ i, subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) k)) (η i) * pderivLin (Sum.inl i) (G₀.toPowerSeries l)
                  + ∑ i, subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) k)) (η i) * pderivLin (Sum.inr i) (G₀.toPowerSeries l)
                  - subst G₀.toPowerSeries (η l) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_mem_firstOrderCoboundaries_iff.solution
