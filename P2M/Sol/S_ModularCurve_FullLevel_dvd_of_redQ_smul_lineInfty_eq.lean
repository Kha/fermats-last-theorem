import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import P2M.Util
namespace P2MW.S_ModularCurve_FullLevel_dvd_of_redQ_smul_lineInfty_eq

set_option autoImplicit false

open scoped MatrixGroups

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup

namespace K1KidsP2

variable (q : ℕ) [Fact q.Prime]

private theorem coe_redQ_apply (δ : SL(2, ℤ)) (i j : Fin 2) :
    ((redQ q δ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j = ((δ i j : ℤ) : ZMod q) := by
  simp [redQ, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

private theorem redQ_smul_lineInfty_eq_iff (δ : SL(2, ℤ)) :
    redQ q δ • lineInfty q = lineInfty q ↔ ((δ 1 0 : ℤ) : ZMod q) = 0 := by
  have hsm : (redQ q δ) • (![1, 0] : Fin 2 → ZMod q) = ![((δ 0 0 : ℤ) : ZMod q), ((δ 1 0 : ℤ) : ZMod q)] := by
    show ((redQ q δ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) • (![1, 0] : Fin 2 → ZMod q) = _
    ext i
    rw [Matrix.smul_eq_mulVec]
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, coe_redQ_apply]
  rw [lineInfty, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  simp only [hsm]
  constructor
  · rintro ⟨a, ha⟩
    have := congr_fun ha 1
    simpa using this.symm
  · intro h
    have hdet : ((δ 0 0 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q) = 1 := by
      have hd := Matrix.det_fin_two (δ : Matrix (Fin 2) (Fin 2) ℤ)
      rw [δ.prop] at hd
      have := congrArg (Int.cast : ℤ → ZMod q) hd
      push_cast at this
      rw [h, mul_zero, sub_zero] at this
      exact this.symm
    refine ⟨Units.mkOfMulEqOne _ _ hdet, ?_⟩
    ext i
    fin_cases i <;> simp [h, Units.smul_def]

end K1KidsP2

theorem solution
    (q : ℕ) [Fact q.Prime] (δ : SL(2, ℤ))
    (hfix : ModularCurve.FullLevel.redQ q δ • ModularCurve.FullLevel.lineInfty q = ModularCurve.FullLevel.lineInfty q) :
    (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 ((K1KidsP2.redQ_smul_lineInfty_eq_iff q δ).1 hfix)
