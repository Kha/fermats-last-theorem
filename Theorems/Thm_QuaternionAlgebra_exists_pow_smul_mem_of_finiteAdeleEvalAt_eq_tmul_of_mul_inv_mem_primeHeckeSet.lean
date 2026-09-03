import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_pow_smul_mem_of_finiteAdeleEvalAt_eq_tmul_of_mul_inv_mem_primeHeckeSet
attribute [-instance] CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction
attribute [-simp] CerednikDrinfeld.HeckeData.mk.sizeOf_spec CerednikDrinfeld.Matching.mk.injEq CerednikDrinfeld.DegeneracyData.mk.sizeOf_spec CerednikDrinfeld.DegeneracyData.mk.injEq CerednikDrinfeld.ribbonGram_apply CerednikDrinfeld.HeckeData.mk.injEq CerednikDrinfeld.Matching.mk.sizeOf_spec ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra

theorem QuaternionAlgebra.exists_pow_smul_mem_of_finiteAdeleEvalAt_eq_tmul_of_mul_inv_mem_primeHeckeSet
    {a₁ b₁ : ℚ} (R₁ O : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsOrder R₁) (hO : O ≤ R₁)
    (r : ℕ) [Fact r.Prime] (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (s : (ℍ[ℚ, a₁, b₁])ˣ) (sf : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₁ : ∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ))
    (hs₃ : Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
        (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr hℓ))) * sf⁻¹ ∈
      primeHeckeSet O ℓ) :
    ∃ a : ℕ, ((r ^ a : ℕ) : ℚ) • ((s : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₁ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_pow_smul_mem_of_finiteAdeleEvalAt_eq_tmul_of_mul_inv_mem_primeHeckeSet.solution
