import Mathlib
import P2M.Util
namespace P2MW.S_Bialgebra_snd_mul_withConv_algHom_dualNumber_eq_add

set_option autoImplicit false

theorem solution
    (k : Type) [CommRing k] (B : Type) [CommRing B] [Bialgebra k B]
    (D₁ D₂ : B →ₐ[k] DualNumber k)
    (h₁ : ∀ b : B, TrivSqZeroExt.fst (D₁ b) = Bialgebra.counitAlgHom k B b)
    (h₂ : ∀ b : B, TrivSqZeroExt.fst (D₂ b) = Bialgebra.counitAlgHom k B b) (b : B) :
    TrivSqZeroExt.snd (WithConv.ofConv (WithConv.toConv D₁ * WithConv.toConv D₂) b) =
      TrivSqZeroExt.snd (D₁ b) + TrivSqZeroExt.snd (D₂ b) := by
  classical

  let 𝓡 := Coalgebra.Repr.arbitrary k b
  have hexp : WithConv.ofConv (WithConv.toConv D₁ * WithConv.toConv D₂) b =
      ∑ i ∈ 𝓡.index, D₁ (𝓡.left i) * D₂ (𝓡.right i) := by
    show (WithConv.toConv D₁ * WithConv.toConv D₂) b = _
    rw [AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv, ← 𝓡.eq, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.lift_tmul]
  rw [hexp, TrivSqZeroExt.snd_sum]
  simp only [TrivSqZeroExt.snd_mul, h₁, h₂, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    Finset.sum_add_distrib]

  have e₂ : ∑ i ∈ 𝓡.index, Bialgebra.counitAlgHom k B (𝓡.left i) * TrivSqZeroExt.snd (D₂ (𝓡.right i)) =
      TrivSqZeroExt.snd (D₂ b) := by
    have h := Coalgebra.sum_counit_smul 𝓡
    conv_rhs => rw [← h]
    rw [map_sum, TrivSqZeroExt.snd_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, TrivSqZeroExt.snd_smul, smul_eq_mul]
    rfl
  have e₁ : ∑ i ∈ 𝓡.index, TrivSqZeroExt.snd (D₁ (𝓡.left i)) * Bialgebra.counitAlgHom k B (𝓡.right i) =
      TrivSqZeroExt.snd (D₁ b) := by
    have h := congrArg (TensorProduct.rid k B) (Coalgebra.sum_tmul_counit_eq (R := k) 𝓡)
    rw [map_sum, TensorProduct.rid_tmul, one_smul] at h
    conv_rhs => rw [← h]
    rw [map_sum, TrivSqZeroExt.snd_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.rid_tmul, map_smul, TrivSqZeroExt.snd_smul, smul_eq_mul, mul_comm]
    rfl
  rw [e₁, e₂, add_comm]
