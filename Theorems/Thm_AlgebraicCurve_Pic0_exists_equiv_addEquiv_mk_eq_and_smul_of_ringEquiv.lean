import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JZeroTateModule
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv
    {K K' F F' : Type} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F']
    (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K' F' (e a)) :
    ∃ (Φ : Place K F ≃ Place K' F') (Ψ : Pic0 K F ≃+ Pic0 K' F'),
      (∀ v : Place K F, (Φ v).toValuationSubring = v.toValuationSubring.comap φ.symm.toRingHom) ∧
      (∀ D : Divisor.degZero (K := K) (F := F),
        ∃ hD : Finsupp.mapDomain Φ (D : Divisor K F) ∈ Divisor.degZero (K := K') (F := F'),
          Ψ (Pic0.mk D) = Pic0.mk ⟨_, hD⟩) ∧
      (∀ (σ : F ≃ₐ[K] F) (σ' : F' ≃ₐ[K'] F'), (∀ f : F, φ (σ f) = σ' (φ f)) →
        ∀ x : Pic0 K F, Ψ (σ • x) = σ' • Ψ x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv.solution
