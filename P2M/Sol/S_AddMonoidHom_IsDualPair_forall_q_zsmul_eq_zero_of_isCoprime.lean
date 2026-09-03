import Mathlib
import Definitions.Def_DualIsogenyAPI
import P2M.Util
namespace P2MW.S_AddMonoidHom_IsDualPair_forall_q_zsmul_eq_zero_of_isCoprime

theorem solution
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (hdual : AddMonoidHom.IsDualPair φ ψ n) (q : ℕ)
    (hcop : IsCoprime n (q : ℤ))
    (hA : ∀ a : A, (q : ℤ) • a = 0 → a = 0) :
    ∀ b : B, (q : ℤ) • b = 0 → b = 0 := by
  intro b hb
  have hqψ : (q : ℤ) • ψ b = 0 := by rw [← map_zsmul, hb, map_zero]
  have hψb : ψ b = 0 := hA (ψ b) hqψ
  have hnb : n • b = 0 := hdual.ker_le_torsion_left hψb
  obtain ⟨u, v, huv⟩ := hcop
  calc b = (1 : ℤ) • b := (one_zsmul b).symm
    _ = (u * n + v * (q : ℤ)) • b := by rw [huv]
    _ = u • n • b + v • (q : ℤ) • b := by rw [add_zsmul, mul_zsmul, mul_zsmul]
    _ = 0 := by simp [hnb, hb]
