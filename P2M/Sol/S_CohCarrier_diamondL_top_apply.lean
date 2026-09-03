import Mathlib
import Definitions.Def_CohCarrier_Inst
import P2M.Util
namespace P2MW.S_CohCarrier_diamondL_top_apply

set_option autoImplicit false

open scoped MatrixGroups
open CongruenceSubgroup

theorem solution (M : ℕ) [NeZero M] (𝒪 : Type) [CommRing 𝒪]
    (d : (ZMod M)ˣ) (φ : CohCarrier.H1 M ⊤ 𝒪) :
    CohCarrier.diamondL M ⊤ 𝒪 d φ = φ := by
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective M d
  rw [CohCarrier.diamondL_eq_diamondRaw M ⊤ 𝒪 d σ hσ]

  have hσmem : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH M ⊤ :=
    CohCarrier.mem_GammaH_iff.mpr ⟨σ.2, Subgroup.mem_top _⟩
  set s : ↥(CohCarrier.GammaH M ⊤) := ⟨(σ : SL(2, ℤ)), hσmem⟩ with hs
  ext a

  change φ (Additive.ofMul (CohCarrier.conjHom M ⊤ σ (Additive.toMul a))) = φ a
  have hconj : CohCarrier.conjHom M ⊤ σ (Additive.toMul a) = s * Additive.toMul a * s⁻¹ :=
    Subtype.ext rfl
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, ofMul_toMul]
  abel
