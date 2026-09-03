import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_JH_exists_pow_smul_tateEnd_fricke_mem_toricLattice_of_degeneracySwap

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JH.exists_pow_smul_tateEnd_fricke_mem_toricLattice_of_degeneracySwap
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)

    (Tt : Submodule ℤ_[p] (TateModule p (JH M H)))
    (push₀ push₁ : TateModule p (JH M H) →ₗ[ℤ_[p]] TateModule p (JH (M / p) (infSubgroup p M H hpM)))
    (pull₀ pull₁ : TateModule p (JH (M / p) (infSubgroup p M H hpM)) →ₗ[ℤ_[p]] TateModule p (JH M H))

    (w : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H)
    (hw3 : ∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x)
    (hwI : ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ x : JH M H,
      SemilinearAut.ofAlgAut w • (σ • x) = σ • (SemilinearAut.ofAlgAut w • x))
    (w' : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≃ₐ[AlgebraicClosure ℚ]
      xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
    (hw3' : ∀ y : JH (M / p) (infSubgroup p M H hpM), SemilinearAut.ofAlgAut w' • (SemilinearAut.ofAlgAut w' • y) = y)

    (hTOR : ∀ τ ∈ Pl.inertiaSubgroupIn ℚ, ∀ x ∈ Tt,
      JH.tateGaloisRep M H p τ x = ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x)

    (hPUSH : ∀ x ∈ Tt, push₀ x = 0 ∧ push₁ x = 0)

    (hCUT : ∃ k : ℕ, ∀ τ ∈ Pl.inertiaSubgroupIn ℚ, ∀ v : TateModule p (JH M H),
      (((p : ℕ) : ℤ_[p]) ^ k) • (JH.tateGaloisRep M H p τ v - v) ∈ Tt ⊔ (LinearMap.range pull₀ ⊔ LinearMap.range pull₁))

    (hOLD : ∀ o ∈ LinearMap.range pull₀ ⊔ LinearMap.range pull₁, push₀ o = 0 → push₁ o = 0 → o = 0)

    (hSWAP : ∀ x : TateModule p (JH M H),
      push₁ (JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut w)) x) =
        JH.tateEnd (M / p) (infSubgroup p M H hpM) p
          (DistribSMul.toAddMonoidHom (JH (M / p) (infSubgroup p M H hpM)) (SemilinearAut.ofAlgAut w')) (push₀ x))

    (hCYC : ∃ τ₀ ∈ Pl.inertiaSubgroupIn ℚ,
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ₀.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p])) :
    ∃ k : ℕ, ∀ x ∈ Tt,
      (((p : ℕ) : ℤ_[p]) ^ k) • JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut w)) x ∈ Tt := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JH_exists_pow_smul_tateEnd_fricke_mem_toricLattice_of_degeneracySwap.solution
