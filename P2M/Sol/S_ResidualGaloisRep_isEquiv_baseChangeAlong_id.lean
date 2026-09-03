import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_GaloisRep_ResidualEquiv
import P2M.Util
namespace P2MW.S_ResidualGaloisRep_isEquiv_baseChangeAlong_id

open scoped TensorProduct

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "IsEquiv baseChangeAlong V ρ"
namespace D5Sol
p2m_open "ResidualGaloisRep"

variable {k : Type} [Field k]

theorem isEquiv_baseChangeAlong_of_apply_eq (ρ : ResidualGaloisRep k) (φ : k →+* k)
    (hφ : ∀ x, φ x = x) : ρ.IsEquiv (ρ.baseChangeAlong φ) := by
  obtain rfl : φ = RingHom.id k := RingHom.ext hφ
  exact ⟨⟨((TensorProduct.lid k ρ.V).symm : ρ.V ≃ₗ[k] (ρ.baseChangeAlong (RingHom.id k)).V),
    fun σ x => rfl⟩⟩

theorem residueFieldMap_algebraMap_self_apply {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    (x : IsLocalRing.ResidueField 𝒪) : IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪) x = x := by
  induction x using Quotient.inductionOn' with
  | h a => rfl

end ResidualGaloisRep.D5Sol

theorem solution {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    ρ.IsEquiv (ρ.baseChangeAlong (RingHom.id k)) :=
  ResidualGaloisRep.D5Sol.isEquiv_baseChangeAlong_of_apply_eq ρ _ fun _ => rfl
