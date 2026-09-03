import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtCitation_KummerBridge

import Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
import P2M.Util
namespace P2MW.S_ExtCitation_exists_isPrimitiveRoot_of_cycloChar_localGaloisToGlobal_eq_one

set_option autoImplicit false
set_option maxHeartbeats 1600000
open ExtCitation

theorem solution (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q))
    (hK : ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, σ ∈ K.fixingSubgroup → cycloChar p (localGaloisToGlobal q σ) = 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ p := by
  obtain ⟨ζ, hζ, hsmul⟩ := ExtCitation.exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal q p

  have hfix : ∀ σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, σ ∈ K.fixingSubgroup → σ ((ζ : (PadicAlgCl q)ˣ) : PadicAlgCl q) = ζ := by
    intro σ hσ
    have h := hsmul σ
    rw [hK σ hσ, Units.val_one, ZMod.val_one, pow_one] at h
    have := congrArg (fun u : (PadicAlgCl q)ˣ => (u : PadicAlgCl q)) h
    exact this
  have hmem : ((ζ : (PadicAlgCl q)ˣ) : PadicAlgCl q) ∈ K := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact hfix σ hσ
  refine ⟨⟨_, hmem⟩, ?_⟩
  have hζ' : IsPrimitiveRoot ((ζ : (PadicAlgCl q)ˣ) : PadicAlgCl q) p := IsPrimitiveRoot.coe_units_iff.2 hζ
  exact IsPrimitiveRoot.coe_submonoidClass_iff.1 hζ'
