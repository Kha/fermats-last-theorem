import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem
AutomorphicForm.sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (L : Type) [Field L] [NumberField L] [Algebra K L] (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : ∀ x : w.1.adicCompletion L,
      θ x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)))
    (φ : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
    (a b : (w.1.adicCompletion L)ˣ) (α β : (v.adicCompletion K)ˣ)
    (hα : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (a : w.1.adicCompletion L))
    (hβ : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (b : w.1.adicCompletion L))
    (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (δ : GL (Fin 2) (w.1.adicCompletion L))
    (hδ : (δ : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![(a : w.1.adicCompletion L), 0; 0, (b : w.1.adicCompletion L)])
    (T : Subgroup (GL (Fin 2) (w.1.adicCompletion L)))
    (hT : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      x ∈ T ↔ x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x = δ)
    (S : Finset (GL (Fin 2) (w.1.adicCompletion L)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T,
      ∀ u ∈ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
          (x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ T,
          ∃ u ∈ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L), x = t * s * u) :
    ∑ x ∈ S,
        (((T ⊓ (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)).map
              (MulAut.conj x).toMonoidHom).relIndex
            (T ⊓ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) : ℕ) : ℂ) *
          (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
            (x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ m *
        ∑ᶠ c : GL (Fin 2) (w.1.adicCompletion L) ⧸
          LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        Set.indicator
          {c : GL (Fin 2) (w.1.adicCompletion L) ⧸
              LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) |
            ∃ g : GL (Fin 2) (w.1.adicCompletion L), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0 = (a : w.1.adicCompletion L) ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 1 = (b : w.1.adicCompletion L)}
          (fun c => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (Quotient.out c)) c := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one.solution
