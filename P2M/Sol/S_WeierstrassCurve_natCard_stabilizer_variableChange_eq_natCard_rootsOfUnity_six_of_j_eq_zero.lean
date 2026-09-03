import Mathlib
import Theorems.Thm_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a4_eq_zero
import P2M.Util
namespace P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero

set_option autoImplicit false

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "toCharNeTwoNF isUnit_Δ VariableChange.mul_def variableChange_c₆ VariableChange.ext c_relation c₄_of_isShortNF IsShortNF a₄ a₆ c₆_of_isShortNF toShortNF c₆ reduction variableChange_c₄ Δ c₄ VariableChange j_eq_zero_iff' j mem_stabilizer_variableChange_iff_of_isShortNF_of_a4_eq_zero"
p2m_open "WeierstrassCurve"

open MulAction

variable {F : Type*} [Field F]

theorem natCard_stabilizer_isShortNF_a₄_eq_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsShortNF] (ha₄ : E.a₄ = 0) (ha₆ : E.a₆ ≠ 0) :
    Nat.card (stabilizer (VariableChange F) E) = Nat.card (rootsOfUnity 6 F) := by
  refine Nat.card_congr
    { toFun := fun C => ⟨C.1.u, (mem_rootsOfUnity' 6 C.1.u).mpr
        ((mem_stabilizer_variableChange_iff_of_isShortNF_of_a4_eq_zero
          h2 h3 E ha₄ ha₆ C.1).mp C.2).2.2.2⟩
      invFun := fun u => ⟨⟨u.1, 0, 0, 0⟩,
        (mem_stabilizer_variableChange_iff_of_isShortNF_of_a4_eq_zero h2 h3 E ha₄ ha₆ _).mpr
          ⟨rfl, rfl, rfl, (mem_rootsOfUnity' 6 u.1).mp u.2⟩⟩
      left_inv := fun C => ?_
      right_inv := fun u => rfl }
  obtain ⟨hr, hs, ht, -⟩ :=
    (mem_stabilizer_variableChange_iff_of_isShortNF_of_a4_eq_zero h2 h3 E ha₄ ha₆ C.1).mp C.2
  exact Subtype.ext (VariableChange.ext rfl hr.symm hs.symm ht.symm)

private lemma coe_1728_ne_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : (1728 : F) ≠ 0 :=
  fun habs => mul_ne_zero (pow_ne_zero 6 h2) (pow_ne_zero 3 h3) (by linear_combination habs)

theorem natCard_stabilizer_eq_card_rootsOfUnity_of_j_eq_zero (h2 : (2 : F) ≠ 0)
    (h3 : (3 : F) ≠ 0) (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 0) :
    Nat.card (stabilizer (VariableChange F) E) = Nat.card (rootsOfUnity 6 F) := by
  letI : Invertible (2 : F) := invertibleOfNonzero h2
  letI : Invertible (3 : F) := invertibleOfNonzero h3
  set E' := E.toShortNF • E with hE'

  have hc₄ : E.c₄ = 0 := pow_eq_zero_iff three_ne_zero |>.mp (E.j_eq_zero_iff'.mp hj)
  have hc₆ : E.c₆ ≠ 0 := by
    intro h
    have hΔ0 : (1728 : F) * E.Δ = 0 := by rw [E.c_relation, hc₄, h]; ring
    exact E.isUnit_Δ.ne_zero ((mul_eq_zero.mp hΔ0).resolve_left (coe_1728_ne_zero h2 h3))

  have hu1 : E.toShortNF.u = 1 := by simp [toShortNF, toCharNeTwoNF, VariableChange.mul_def]
  have hc₄' : E'.c₄ = E.c₄ := by
    rw [hE', variableChange_c₄, hu1, inv_one, Units.val_one, one_pow, one_mul]
  have hc₆' : E'.c₆ = E.c₆ := by
    rw [hE', variableChange_c₆, hu1, inv_one, Units.val_one, one_pow, one_mul]
  have h48 : (-48 : F) ≠ 0 := fun habs =>
    mul_ne_zero (pow_ne_zero 4 h2) h3 (by linear_combination -habs)
  have ha₄' : E'.a₄ = 0 := by
    have h := hc₄'.trans hc₄
    rw [E'.c₄_of_isShortNF] at h
    exact (mul_eq_zero.mp h).resolve_left h48
  have ha₆' : E'.a₆ ≠ 0 := fun h => hc₆ (by rw [← hc₆', E'.c₆_of_isShortNF, h, mul_zero])
  calc Nat.card (stabilizer (VariableChange F) E)
      = Nat.card (stabilizer (VariableChange F) E') :=
        Nat.card_congr (stabilizerEquivStabilizer (G := VariableChange F)
          (g := E.toShortNF) (a := E) (b := E') hE').toEquiv
    _ = Nat.card (rootsOfUnity 6 F) :=
        natCard_stabilizer_isShortNF_a₄_eq_zero h2 h3 E' ha₄' ha₆'

end WeierstrassCurve

theorem solution
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) =
      Nat.card (rootsOfUnity 6 F) :=
  WeierstrassCurve.natCard_stabilizer_eq_card_rootsOfUnity_of_j_eq_zero h2 h3 E hj
