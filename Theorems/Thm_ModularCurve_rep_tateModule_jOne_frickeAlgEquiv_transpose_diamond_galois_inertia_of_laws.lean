import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_rep_tateModule_jOne_frickeAlgEquiv_transpose_diamond_galois_inertia_of_laws

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.rep_tateModule_jOne_frickeAlgEquiv_transpose_diamond_galois_inertia_of_laws
    (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hIn : HeckeDiamondInputsAll M) (hcomm : HeckeDiamondCommuteBar M)
    (w : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M)

    (htransp : ∀ (ℓ : ℕ) [Fact ℓ.Prime]
        (hα : HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
        (hβ : HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
        [HasPrincipalDivisors (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ)))]
        (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
          (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hβ)
        (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ))
        (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
          (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hfinα)
        (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
          (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hα)
        (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ))
        (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
          (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hfinβ)
        (x : JOne M),
      heckePic0OneBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
        = SemilinearAut.ofAlgAut w • heckePic0OneBar hα hβ hFIβ hfinα hNα x)

    (hdiamond : ∀ (d : ℕ) (x : JOne M),
      diamondOneBar M d (SemilinearAut.ofAlgAut w • diamondOneBar M d x)
        = SemilinearAut.ofAlgAut w • x)

    (hinv : ∀ x : JOne M, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x)

    (htwist : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ), c.Coprime M →
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) → ∀ x : JOne M,
        SemilinearAut.ofAlgAut w • (σ • x)
          = σ • diamondOneBar M c (SemilinearAut.ofAlgAut w • x)) :
    letI := heckeModuleOneBar M

    (∀ x : TateModule p (JOne M),
      TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
          (SemilinearAut.ofAlgAut w)
        (TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
          (SemilinearAut.ofAlgAut w) x) = x) ∧

    (∀ d : ℕ,
      tateHeckeRepOne p (JOne M) (diamondGen d) =
        TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
          (SemilinearAut.ofAlgAut (diamondAutBar M d)) ∧
      ∀ x : TateModule p (JOne M),
        tateHeckeRepOne p (JOne M) (diamondGen d)
          (TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
            (SemilinearAut.ofAlgAut w) (tateHeckeRepOne p (JOne M) (diamondGen d) x)) =
        TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
          (SemilinearAut.ofAlgAut w) x) ∧

    (∀ (ℓ : ℕ) [Fact ℓ.Prime]
        (hα : HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
        (hβ : HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
        [HasPrincipalDivisors (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ)))],
      (∀ (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hfinα)
          (x : TateModule p (JOne M)) (n : ℕ),
        ((tateHeckeRepOne p (JOne M) (heckeGenOne ⟨ℓ, Fact.out⟩) x : TateModule p (JOne M)) :
            ℕ → JOne M) n =
          Pic0.correspondence (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hβ hα hFIβ hfinα hNα
            ((x : ℕ → JOne M) n)) ∧
      (∀ (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hfinβ)
          (C' : TateModule p (JOne M) →ₗ[ℤ_[p]] TateModule p (JOne M)),
        (∀ (b : TateModule p (JOne M)) (n : ℕ),
          ((C' b : TateModule p (JOne M)) : ℕ → JOne M) n =
            Pic0.correspondence (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ)
              (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hα hβ hFIα hfinβ hNβ
              ((b : ℕ → JOne M) n)) →
        ∀ x : TateModule p (JOne M),
          C' (TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
              (SemilinearAut.ofAlgAut w) x) =
            TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
              (SemilinearAut.ofAlgAut w)
              (tateHeckeRepOne p (JOne M) (heckeGenOne ⟨ℓ, Fact.out⟩) x))) ∧

    ((∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : TateModule p (JOne M),
          TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
              (SemilinearAut.ofAlgAut w)
              (TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) =
            TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
              (tateHeckeRepOne p (JOne M) (diamondGen c)
                (TateModule.rep p (JOne M)
                  (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
                  (SemilinearAut.ofAlgAut w) x))) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ) →
        ∀ x : TateModule p (JOne M),
          TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
              (SemilinearAut.ofAlgAut w)
              (TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) =
            TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
              (TateModule.rep p (JOne M)
                (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
                (SemilinearAut.ofAlgAut w) x))) ∧

    (∀ (q : ℕ), q.Prime → q ∣ M → ¬ q ^ 2 ∣ M →
      ∀ (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime q →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ x : TateModule p (JOne M),
        (∀ (n : ℕ), ∀ d ∈ normFreeRepsAt M q,
          diamondOneBar M d ((x : ℕ → JOne M) n) = (x : ℕ → JOne M) n) →
        TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
            (SemilinearAut.ofAlgAut w)
            (TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ x) =
          TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ
            (TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
              (SemilinearAut.ofAlgAut w) x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_rep_tateModule_jOne_frickeAlgEquiv_transpose_diamond_galois_inertia_of_laws.solution
