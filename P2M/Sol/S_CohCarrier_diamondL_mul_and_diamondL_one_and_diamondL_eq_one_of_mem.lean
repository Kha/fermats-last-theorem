import Definitions.Def_CohCarrier_Inst
import P2M.Util
namespace P2MW.S_CohCarrier_diamondL_mul_and_diamondL_one_and_diamondL_eq_one_of_mem

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace DiamondActionSol

open CongruenceSubgroup
open scoped MatrixGroups

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : Type) [AddCommGroup A]

theorem diamondRaw_apply (σ : Gamma0 M) (φ : CohCarrier.H1 M H A)
    (a : Additive ↥(CohCarrier.GammaH M H)) :
    CohCarrier.diamondRaw M H A σ φ a =
      φ (Additive.ofMul (CohCarrier.conjHom M H σ (Additive.toMul a))) := rfl

theorem diamondRaw_mul (σ τ : Gamma0 M) (φ : CohCarrier.H1 M H A) :
    CohCarrier.diamondRaw M H A (σ * τ) φ =
      CohCarrier.diamondRaw M H A τ (CohCarrier.diamondRaw M H A σ φ) := by
  refine AddMonoidHom.ext fun a => ?_
  simp only [diamondRaw_apply, toMul_ofMul]
  congr 2
  apply Subtype.ext
  simp only [CohCarrier.conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, mul_inv_rev]
  group

theorem diamondRaw_one (φ : CohCarrier.H1 M H A) : CohCarrier.diamondRaw M H A 1 φ = φ := by
  refine AddMonoidHom.ext fun a => ?_
  rw [diamondRaw_apply]
  congr 1
  have : CohCarrier.conjHom M H 1 (Additive.toMul a) = Additive.toMul a := by
    apply Subtype.ext
    simp [CohCarrier.conjHom]
  rw [this, ofMul_toMul]

theorem diamondRaw_eq_self_of_mem (σ : Gamma0 M) (hσ : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H)
    (φ : CohCarrier.H1 M H A) : CohCarrier.diamondRaw M H A σ φ = φ := by
  set κ : ↥(CohCarrier.GammaH M H) := ⟨(σ : SL(2, ℤ)), hσ⟩ with hκ
  refine AddMonoidHom.ext fun a => ?_
  rw [diamondRaw_apply]
  have hconj : CohCarrier.conjHom M H σ (Additive.toMul a) = κ * Additive.toMul a * κ⁻¹ := by
    apply Subtype.ext
    simp [CohCarrier.conjHom, hκ]
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, ofMul_toMul]
  abel

variable [NeZero M] (𝒪 : Type) [CommRing 𝒪]

theorem diamondL_mul (u v : (ZMod M)ˣ) (φ : CohCarrier.H1 M H 𝒪) :
    CohCarrier.diamondL M H 𝒪 (u * v) φ =
      CohCarrier.diamondL M H 𝒪 u (CohCarrier.diamondL M H 𝒪 v φ) := by
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective M u
  obtain ⟨τ, hτ⟩ := CohCarrier.gamma0Units_surjective M v
  have hlift : CohCarrier.gamma0Units M (τ * σ) = u * v := by rw [map_mul, hσ, hτ, mul_comm]
  rw [CohCarrier.diamondL_eq_diamondRaw M H 𝒪 (u * v) (τ * σ) hlift, diamondRaw_mul,
    CohCarrier.diamondL_eq_diamondRaw M H 𝒪 v τ hτ, CohCarrier.diamondL_eq_diamondRaw M H 𝒪 u σ hσ]

theorem diamondL_one (φ : CohCarrier.H1 M H 𝒪) : CohCarrier.diamondL M H 𝒪 1 φ = φ := by
  rw [CohCarrier.diamondL_eq_diamondRaw M H 𝒪 1 1 (map_one _), diamondRaw_one]

theorem diamondL_eq_self_of_mem (u : (ZMod M)ˣ) (hu : u ∈ H) (φ : CohCarrier.H1 M H 𝒪) :
    CohCarrier.diamondL M H 𝒪 u φ = φ := by
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective M u
  rw [CohCarrier.diamondL_eq_diamondRaw M H 𝒪 u σ hσ]
  refine diamondRaw_eq_self_of_mem M H 𝒪 σ ?_ φ
  rw [CohCarrier.mem_GammaH_iff]
  exact ⟨σ.2, by rw [Subtype.coe_eta, hσ]; exact hu⟩

end DiamondActionSol

open DiamondActionSol in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪] :
    (∀ u v : (ZMod M)ˣ, CohCarrier.diamondL M H 𝒪 (u * v) =
        CohCarrier.diamondL M H 𝒪 u * CohCarrier.diamondL M H 𝒪 v) ∧
    CohCarrier.diamondL M H 𝒪 1 = 1 ∧
    (∀ u ∈ H, CohCarrier.diamondL M H 𝒪 u = 1) :=
  ⟨fun u v => LinearMap.ext fun φ => diamondL_mul M H 𝒪 u v φ,
    LinearMap.ext fun φ => diamondL_one M H 𝒪 φ,
    fun u hu => LinearMap.ext fun φ => diamondL_eq_self_of_mem M H 𝒪 u hu φ⟩
