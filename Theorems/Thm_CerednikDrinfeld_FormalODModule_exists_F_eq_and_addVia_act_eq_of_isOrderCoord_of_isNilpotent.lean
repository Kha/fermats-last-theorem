import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent
attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup
attribute [-simp] MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped Quaternion

theorem CerednikDrinfeld.FormalODModule.exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : CerednikDrinfeld.QM.IsOrderCoord Λ q coord)
    (B : Type u) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B))
    (F : MvFormalGroup 2 B) [F.IsComm] (ρ : ↥Λ → MvFormalGroup.End F)
    (hadd : ∀ m m' : ↥Λ, ρ (m + m') = ρ m + ρ m')
    (hmul : ∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = ρ m * ρ m')
    (hunit : ∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0) ∧
        (ρ ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩).toPowerSeries = F.nthSeries n) :
    ∃ X : FormalODModule q B, X.F = F ∧
      ∀ m : ↥Λ, Series.addVia F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) =
        (ρ m).toPowerSeries := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent.solution
