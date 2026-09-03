import Definitions.Def_ModularCurve_JZeroTateModule
import P2M.Util
import P2M.Sol.S_TateModule_add_one_le_finrank_span_tmul_add_of_forall_proj_rel_coboundary

set_option autoImplicit false

open scoped TensorProduct

theorem TateModule.add_one_le_finrank_span_tmul_add_of_forall_proj_rel_coboundary
    (ℓ : ℕ) [Fact ℓ.Prime] (J : Type) [AddCommGroup J]
    (n m : ℕ) (hn : 0 < n) (src tgt : Fin m → Fin n)
    (κ : Type) [Field κ] (ζ : ℕ → κ) (hζ0 : ζ 0 = 1) (hζ : ∀ k, ζ (k + 1) ^ ℓ = ζ k) (hζ1 : ζ 1 ≠ 1)
    (x : Fin m → TateModule ℓ J)
    (H : ∀ (k : ℕ) (c : Fin m → ℤ), (∑ e, c e • TateModule.proj ℓ J k (x e)) = 0 →
      ∃ b : Fin n → κ, (∀ i, b i ≠ 0) ∧ ∀ e, ζ k ^ (c e) * b (src e) = b (tgt e))
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ J)]
    :
    m + 1 ≤ Module.finrank ℚ_[ℓ] ↥(Submodule.span ℚ_[ℓ]
      (Set.range fun e : Fin m => ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x e : ModularCurve.RationalTateModule ℓ J))) + n := by p2m_exact_reverting @_root_.P2MW.S_TateModule_add_one_le_finrank_span_tmul_add_of_forall_proj_rel_coboundary.solution
