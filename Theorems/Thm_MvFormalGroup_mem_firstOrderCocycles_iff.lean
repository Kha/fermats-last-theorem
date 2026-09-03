import Mathlib
import Definitions.Def_MvFormalGroup_FirstOrderDeformation
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
import P2M.Sol.S_MvFormalGroup_mem_firstOrderCocycles_iff

set_option autoImplicit false

open MvPowerSeries MvFormalGroup
theorem MvFormalGroup.mem_firstOrderCocycles_iff
    {k : Type} [Field k] {d : ℕ} (G₀ : MvFormalGroup d k) [G₀.IsComm]
    (z : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :
    let XY : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
      Sum.elim (fun l => X (Sum.inl l)) (fun l => X (Sum.inr (Sum.inl l)))
    let YZ : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
      Sum.elim (fun l => X (Sum.inr (Sum.inl l))) (fun l => X (Sum.inr (Sum.inr l)))
    let famL : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
      Sum.elim (fun j => subst XY (G₀.toPowerSeries j)) (fun j => X (Sum.inr (Sum.inr j)))
    let famR : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
      Sum.elim (fun j => X (Sum.inl j)) (fun j => subst YZ (G₀.toPowerSeries j))
    z ∈ firstOrderCocycles G₀ ↔
      ((∀ l, constantCoeff (z l) = 0) ∧
       (∀ l j, coeff (Finsupp.single (Sum.inl j) 1) (z l) = 0 ∧ coeff (Finsupp.single (Sum.inr j) 1) (z l) = 0) ∧
       (∀ l, subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) k)) fun j => X (Sum.inl j)) (z l) = z l) ∧
       (∀ l, subst famL (z l) + ∑ i, subst XY (z i) * subst famL (pderivLin (Sum.inl i) (G₀.toPowerSeries l))
            = subst famR (z l) + ∑ i, subst YZ (z i) * subst famR (pderivLin (Sum.inr i) (G₀.toPowerSeries l)))) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_mem_firstOrderCocycles_iff.solution
