import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LatticeTreeOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_orbitalIntegral_eq_shadow_of_irreducible_charpoly
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    [Finite ((v.adicCompletionIntegers K) ⧸ Ideal.span {ϖ})]
    (hfin : ∀ g : GL (Fin 2) (v.adicCompletion K),
      (QuotientGroup.mk '' ((LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) : Set (GL (Fin
          2) (v.adicCompletion K))) * {g}) :
        Set (GL (Fin 2) (v.adicCompletion K) ⧸ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion
            K))).Finite)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (u : (v.adicCompletionIntegers K)ˣ) (D : ℤ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u * algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K) ϖ ^ D)
    (S : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : S (HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖ hϖ0) (hfin _)) =
      (Nat.card ((v.adicCompletionIntegers K) ⧸ Ideal.span {ϖ}) : ℂ) • AddMonoidAlgebra.single ((1 : ℤ), (0 : ℤ)) 1 +
        AddMonoidAlgebra.single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : S (HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖ hϖ0 * LocalGL2.localRepInf ϖ hϖ0) (hfin _)) =
      AddMonoidAlgebra.single ((1 : ℤ), (1 : ℤ)) 1)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
        (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ)
    (hC : (LT.LatticeTree.fixedVertexSet (R := v.adicCompletionIntegers K) γ).Finite)
    (hTZ : ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range) ⊔
          Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex (Subgroup.centralizer ({γ} : Set (GL (Fin 2)
              (v.adicCompletion K)))) ≠ 0)
    (hm : (τ (((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range)).subgroupOf
            (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : Set (Subgroup.centralizer ({γ} : Set
                (GL (Fin 2) (v.adicCompletion K)))))).toReal ≠ 0)
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) (I :
        ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) I) :
    I = ((((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range) ⊔
              Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex (Subgroup.centralizer ({γ} : Set (GL (Fin 2)
                  (v.adicCompletion K)))) : ℂ) *
          ((τ (((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range)).subgroupOf
              (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : Set (Subgroup.centralizer ({γ} :
                  Set (GL (Fin 2) (v.adicCompletion K)))))).toReal : ℂ))⁻¹ *
      ((if Even D then (LT.LatticeTree.unitOrbitalCount (v.adicCompletionIntegers K) γ : ℂ) * (S f).coeff (D / 2, D /
          2) else 0) +
        2 * (S f).coeff.sum fun (x : ℤ × ℤ) (r : ℂ) => if x.1 < x.2 ∧ x.1 + x.2 = D then r else 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_orbitalIntegral_eq_shadow_of_irreducible_charpoly.solution
