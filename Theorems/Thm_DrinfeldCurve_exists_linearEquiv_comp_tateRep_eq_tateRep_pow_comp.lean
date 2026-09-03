import Definitions.Def_DrinfeldCurve_TateRep
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_exists_linearEquiv_comp_tateRep_eq_tateRep_pow_comp

set_option autoImplicit false

open scoped TensorProduct

theorem DrinfeldCurve.exists_linearEquiv_comp_tateRep_eq_tateRep_pow_comp
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [PerfectField k] [Algebra (GaloisField q 2) k]
    [IsDomain (DrinfeldCurve.CoordRing q k)] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type*) [Field E] [Algebra ℚ_[ℓ] E] :
    ∃ Fr : (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
          (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) ≃ₗ[E]
        (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
          (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))),
      ∀ (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) (α : (GaloisField q 2)ˣ)
        (h : (g, α) ∈ DrinfeldCurve.hSubgroup q) (h' : (g, α ^ q) ∈ DrinfeldCurve.hSubgroup q),
        (Fr : (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
              (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) →ₗ[E]
            (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
              (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k)))) ∘ₗ
            DrinfeldCurve.tateRep q k ℓ E ⟨(g, α), h⟩ =
          DrinfeldCurve.tateRep q k ℓ E ⟨(g, α ^ q), h'⟩ ∘ₗ
            (Fr : (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
                (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k))) →ₗ[E]
              (E ⊗[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ
                (AlgebraicCurve.Pic0 k (DrinfeldCurve.drinfeldFunctionField q k)))) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_exists_linearEquiv_comp_tateRep_eq_tateRep_pow_comp.solution
