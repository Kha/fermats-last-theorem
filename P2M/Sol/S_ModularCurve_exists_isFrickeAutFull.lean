module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Sol.S_ModularCurve_exists_isFrickeAut
import P2M.Sol.S_ModularCurve_full_eq_of_prime
import P2M.Util

namespace P2MW.S_ModularCurve_exists_isFrickeAutFull

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_isFrickeAutFull.ModularCurve AlgebraicCurve IntermediateField"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IsFrickeAutFull qExpand qExpand_one_apply jq jqN modularFunctionField modularFunctionFieldFull exists_isFrickeAut full_eq_of_prime"
p2m_open "ModularCurve"

namespace W2B

theorem cast_algEquiv_exists {E E' : IntermediateField ℚ (LaurentSeries ℚ)} (h : E = E') (σ : E ≃ₐ[ℚ] E) :
    ∃ σ' : E' ≃ₐ[ℚ] E', ∀ x : E', ((σ' x : E') : LaurentSeries ℚ) = σ ⟨x, h ▸ x.2⟩ := by
  subst h
  exact ⟨σ, fun _ => rfl⟩

end W2B

end ModularCurve

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ, IsFrickeAutFull ℓ σ := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have hfull : modularFunctionFieldFull ℓ = modularFunctionField ℓ := ModularCurve.full_eq_of_prime hℓ.out
  obtain ⟨σ, hσ⟩ := ModularCurve.exists_isFrickeAut ℓ
  obtain ⟨σ', hσ'⟩ := ModularCurve.W2B.cast_algEquiv_exists hfull.symm σ
  refine ⟨σ', ?_⟩
  intro a b hab _ _
  have hcases : a = 1 ∧ ℓ = b ∨ ℓ = a ∧ b = 1 := by
    have hprime : (a * b).Prime := hab ▸ hℓ.out
    rcases Nat.prime_mul_iff.mp hprime with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · right; exact ⟨hab.symm.trans (mul_one a), rfl⟩
    · left; exact ⟨rfl, hab.symm.trans (one_mul b)⟩

  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have H : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionField ℓ), y = jq →
        ((σ ⟨y, hy⟩ : modularFunctionField ℓ) : LaurentSeries ℚ) = qExpand ℚ ℓ jq := by
      rintro y hy rfl
      exact congrArg Subtype.val hσ.1
    apply Subtype.ext
    rw [hσ']
    exact H _ _ (qExpand_one_apply jq)
  · have H : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionField ℓ), y = jqN ℓ →
        ((σ ⟨y, hy⟩ : modularFunctionField ℓ) : LaurentSeries ℚ) = qExpand ℚ 1 jq := by
      rintro y hy rfl
      exact (congrArg Subtype.val hσ.2).trans (qExpand_one_apply jq).symm
    apply Subtype.ext
    rw [hσ']
    exact H _ _ rfl

end
end S_ModularCurve_exists_isFrickeAutFull
end P2MW

public section
open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.exists_isFrickeAutFull (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ, IsFrickeAutFull ℓ σ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isFrickeAutFull.solution
end
