import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LatticeTreeOrbital
import Definitions.Def_TwistedNormClasses
import P2M.Util
import P2M.Sol.S_AutomorphicForm_twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly
attribute [-simp] LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions Pointwise

theorem AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) (hσn : σ ^ Module.finrank K L = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum.Extension (𝓞 L) v)
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (θ : LT.LatticeTree.IntegralAut (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
    (hθ : ∀ x : (w.1.adicCompletion L),
      θ.toField x = e (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ (e.symm x)))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (ϖ' : w.1.adicCompletionIntegers L)
    (hϖ' : (ϖ' : (w.1.adicCompletion L)) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ :
        (v.adicCompletion K)))
    (hϖ'0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ' ≠ 0)
    [Finite ((v.adicCompletionIntegers K) ⧸ Ideal.span {ϖ})] [Finite ((w.1.adicCompletionIntegers L) ⧸ Ideal.span
        {ϖ'})]
    (hres : Nat.card ((w.1.adicCompletionIntegers L) ⧸ Ideal.span {ϖ'}) = Nat.card ((v.adicCompletionIntegers K) ⧸
        Ideal.span {ϖ}) ^ Module.finrank K L)
    (hfin : ∀ g : GL (Fin 2) (w.1.adicCompletion L),
      (QuotientGroup.mk '' ((LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) : Set (GL
          (Fin 2) (w.1.adicCompletion L))) * {g}) :
        Set (GL (Fin 2) (w.1.adicCompletion L) ⧸ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L)
            (w.1.adicCompletion L))).Finite)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (δ' : GL (Fin 2) (w.1.adicCompletion L)) (hδ' : δ' = Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom δ)
    (hnorm : LT.TwistedNorm.sigmaNormPow θ.mapGL (Module.finrank K L) δ' =
      Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)) γ)
    (k : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det (δ' : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ * algebraMap (w.1.adicCompletionIntegers L)
          (w.1.adicCompletion L) ϖ' ^ k)
    (S : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ
        →ₐ[ℂ] AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : S (HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖ' hϖ'0) (hfin _)) =
      (Nat.card ((w.1.adicCompletionIntegers L) ⧸ Ideal.span {ϖ'}) : ℂ) • AddMonoidAlgebra.single ((1 : ℤ), (0 : ℤ)) 1
          +
        AddMonoidAlgebra.single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : S (HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖ' hϖ'0 * LocalGL2.localRepInf ϖ' hϖ'0) (hfin _)) =
      AddMonoidAlgebra.single ((1 : ℤ), (1 : ℤ)) 1)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ) (AutomorphicForm.twistedCentralizerBorel K L
        (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hC : (LT.LatticeTree.twistedFixedVertexSet δ' θ).Finite)
    (hTZ : ((AutomorphicForm.sigmaCentralizer θ.mapGL δ' ⊓
              Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (w.1.adicCompletion L) →* (w.1.adicCompletion
                  L)ˣ)
                (Units.map (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)).toMonoidHom).range) ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex (AutomorphicForm.sigmaCentralizer θ.mapGL δ') ≠
              0)
    (hm : (τ' ((((AutomorphicForm.sigmaCentralizer θ.mapGL δ' ⊓
              Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (w.1.adicCompletion L) →* (w.1.adicCompletion
                  L)ˣ)
                (Units.map (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion
                    L)).toMonoidHom).range)).comap
            (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2)
                (w.1.adicCompletion L))).subgroupOf (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal ≠ 0)
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) (I
        : ℂ)
    (hI : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (AutomorphicForm.semiLocalHaar K L v) δ
        τ'
      (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom y)) I)
          :
    I = ((((AutomorphicForm.sigmaCentralizer θ.mapGL δ' ⊓
              Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (w.1.adicCompletion L) →* (w.1.adicCompletion
                  L)ˣ)
                (Units.map (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)).toMonoidHom).range) ⊔
              Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex (AutomorphicForm.sigmaCentralizer θ.mapGL
                  δ') : ℂ) *
          ((τ' ((((AutomorphicForm.sigmaCentralizer θ.mapGL δ' ⊓
              Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (w.1.adicCompletion L) →* (w.1.adicCompletion
                  L)ˣ)
                (Units.map (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion
                    L)).toMonoidHom).range)).comap
              (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin
                  2) (w.1.adicCompletion L))).subgroupOf (twistedCentralizer K L (v.adicCompletion K) σ δ) :
            Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal : ℂ))⁻¹ *
      ((if Even k then (LT.LatticeTree.twistedUnitOrbitalCount δ' θ : ℂ) * (S f).coeff (k / 2, k / 2) else 0) +
        2 * (S f).coeff.sum fun (x : ℤ × ℤ) (r : ℂ) => if x.1 < x.2 ∧ x.1 + x.2 = k then r else 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly.solution
