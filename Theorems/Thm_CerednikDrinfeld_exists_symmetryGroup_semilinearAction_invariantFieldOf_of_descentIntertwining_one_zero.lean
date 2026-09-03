import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero

    {a₂ b₂ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₂ : IsDefiniteRamifiedExactlyAt a₂ b₂ q)
    (Λ₂ R₂ : Submodule ℤ ℍ[ℚ, a₂, b₂]) (hΛ₂ : IsMaximalOrder Λ₂) (hR₂ : IsEichlerOrder R₂ N) (hRΛ₂ : R₂ ≤ Λ₂)
    (n₂ : (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₂ : n₂ ∈ primeHeckeSet R₂ q')
    (hS₂ : IsEichlerOrder (meetOrder R₂ n₂) (N * q'))
    (hnorm₂ : Submodule.conjByFiniteIdele (meetOrder R₂ n₂) n₂ = meetOrder R₂ n₂)
    (hsq₂ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)),
      classSetShift _ n₂ (classSetShift _ n₂ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    (hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂)

    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')

    (FN : Type) [Field FN] [Algebra (AlgebraicClosure ℚ) FN] [IsCurveOver (AlgebraicClosure ℚ) FN]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) FN]
    (𝕋 : HeckeTower.TowerData q q' FN)
    (hfg : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))
    (galN : ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) FN)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (hgalN : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galN τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (hgalT : ∀ ℓ (τ : ↥(A₁.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galT ℓ τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) FN) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

    [hiso₁ : Fact (A₁.DecompositionIsometric ℚ)]
    (v₁ : HeightOneSpectrum (𝓞 ℚ)) (hv₁ : ((q' : ℕ) : 𝓞 ℚ) ∈ v₁.asIdeal)

    (ι₁ : ℍ[ℚ, a₂, b₂] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (hι₁ : Function.Injective ι₁)
    (ρ₁ : (ℍ[ℚ, a₂, b₂])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₁)))
    (hρ₁ : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, ρ₁ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) x))

    (ϖ₁ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hϖ₁ : algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion ϖ₁.ϖ = ((q' : AlgebraicClosure ℚ) : A₁.valuation.Completion))
    [hdom₁ : IsDomain (Omega.HolRingOf ϖ₁ ρ₁)]

    (s₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (sf₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₁ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₁ ℓ : ℍ[ℚ, a₂, b₂]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₂, b₂]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₁ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₂ (meetOrder R₂ n₂) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₂ n₂) (ℓ.1 : ℕ)) ∧
      nrd (s₁ ℓ : ℍ[ℚ, a₂, b₂]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₁ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₂, b₂])ˣ)
    (hΓ₁0 : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, x ∈ Γ₁ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ Even (padicValRat q' (nrd (x : ℍ[ℚ, a₂, b₂]))))
    (hΓ₁ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₁ (some ℓ) = Γ₁ none ⊓ (Γ₁ none).map (MulAut.conj (s₁ ℓ)).toMonoidHom)

    (w₁ wbar₁ : HeckeTower.Obj q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (hw₁ : (w₁ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ nrd (w₁ none : ℍ[ℚ, a₂, b₂]) = (q' : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₁ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁ ∧ nrd (w₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q' : ℚ))
    (hwbar₁ :
      (nrd (wbar₁ none : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₁ none) ∈ Submodule.localBoxUnits R₂ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox R₂ u ↔
            x ∈ Submodule.localBox R₂ u) ∧
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
            x ∈ Submodule.localBox Λ₂ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₁ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₂ (sf₁ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
              x ∈ Submodule.localBox Λ₂ u))))

    (dIso₁ : ↥(A₁.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hdIso₁ : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : A₁.valuation.Completion), (dIso₁ τ).toRingEquiv x = τ • x)

    (χ₁ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (ιM₁ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁))
    (hI : CerednikDrinfeld.DescentIntertwining q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
      FN 𝕋 galN galT W WT χ₁ ιM₁) :
∃ (S₁ : Type) (_ : Group S₁) (scalar₁ : S₁ →* ↥(A₁.decompositionSubgroup ℚ))
      (ιS₁ : ↥(A₁.decompositionSubgroup ℚ) →* S₁) (_ : ∀ τ, scalar₁ (ιS₁ τ) = τ)

      (σ₀₁ σ₁₁ : S₁)
      (χS₁ : S₁ →* Multiplicative (ZMod 2))

      (galF₁ : ∀ j : HeckeTower.Obj q q', S₁ →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.objField j))

      (galFC₁ : ∀ j : HeckeTower.Obj q q',
        S₁ →* SemilinearAut A₁.valuation.Completion ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)))

      (sgn₁ : S₁ →* ℤˣ),

      (∀ σ : S₁, ∃ (τ : ↥(A₁.decompositionSubgroup ℚ)) (u v : ℕ), σ = ιS₁ τ * σ₀₁ ^ u * σ₁₁ ^ v) ∧
      scalar₁ σ₀₁ = 1 ∧ scalar₁ σ₁₁ = 1 ∧ σ₀₁ * σ₀₁ = 1 ∧ σ₁₁ * σ₁₁ = 1 ∧
      σ₀₁ * σ₁₁ = σ₁₁ * σ₀₁ ∧ (∀ τ, ιS₁ τ * σ₀₁ = σ₀₁ * ιS₁ τ) ∧ (∀ τ, ιS₁ τ * σ₁₁ = σ₁₁ * ιS₁ τ) ∧

      (∀ (H : Type) [Group H] (f : ↥(A₁.decompositionSubgroup ℚ) →* H) (h₀ h₂ : H),
        h₀ * h₀ = 1 → h₂ * h₂ = 1 → h₀ * h₂ = h₂ * h₀ → (∀ τ, f τ * h₀ = h₀ * f τ) → (∀ τ, f τ * h₂ = h₂ * f τ) →
        ∃ F : S₁ →* H, (∀ τ, F (ιS₁ τ) = f τ) ∧ F σ₀₁ = h₀ ∧ F σ₁₁ = h₂) ∧

      (∀ j (σ : S₁) (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (galF₁ j σ) a =
        ((scalar₁ σ : ↥(A₁.decompositionSubgroup ℚ)) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), galF₁ none (ιS₁ τ) = galN τ) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (τ : ↥(A₁.decompositionSubgroup ℚ)), galF₁ (some ℓ) (ιS₁ τ) = galT ℓ τ) ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₁) (x : 𝕋.objField (HeckeTower.cod α)),
        galF₁ (HeckeTower.dom α) σ • (show 𝕋.objField (HeckeTower.dom α) from 𝕋.φ α x) =
          (show 𝕋.objField (HeckeTower.dom α) from 𝕋.φ α (galF₁ (HeckeTower.cod α) σ • x))) ∧
      galF₁ none σ₀₁ = W 1 ∧ galF₁ none σ₁₁ = W 0 ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', galF₁ (some ℓ) σ₀₁ = WT ℓ 1 ∧ galF₁ (some ℓ) σ₁₁ = WT ℓ 0) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) = χ₁ τ) ∧ χS₁ σ₀₁ ≠ 1 ∧ χS₁ σ₁₁ = 1 ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ),
        (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₁.inertiaSubgroupIn ℚ → χS₁ (ιS₁ τ) = 1) ∧
      (∀ φ : ↥(A₁.decompositionSubgroup ℚ),
        A₁.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q' → χS₁ (ιS₁ φ) ≠ 1) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) = 1 ↔
        ∀ x : IsLocalRing.ResidueField ↥A₁, x ^ (q' ^ 2) = x → τ • x = x) ∧

      (∀ j (σ : S₁) (c : A₁.valuation.Completion),
        SemilinearAut.baseAut (galFC₁ j σ) c = (scalar₁ σ) • c) ∧
      (∀ j (σ : S₁) (c : A₁.valuation.Completion),
        SemilinearAut.baseAut (galFC₁ j σ) c = (dIso₁ (scalar₁ σ)).toRingEquiv c) ∧
      (∀ j (c : A₁.valuation.Completion), SemilinearAut.baseAut (galFC₁ j σ₀₁) c = c) ∧
      (∀ j (c : A₁.valuation.Completion), SemilinearAut.baseAut (galFC₁ j σ₁₁) c = c) ∧
      (∀ j (σ : S₁) (x : 𝕋.objField j) (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = ιM₁ j x →
          ((galFC₁ j σ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = ιM₁ j (galF₁ j σ • x)) ∧
      (∀ j (τ : ↥(A₁.decompositionSubgroup ℚ)) (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        ((galFC₁ j (ιS₁ τ) • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
          (if χ₁ τ = 1 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else w₁ j) •
            Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ τ)) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧
      (∀ j (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        ((galFC₁ j σ₀₁ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (w₁ j) • (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧
      (∀ j (y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))),
        ((galFC₁ j σ₁₁ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (wbar₁ j) • (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧

      (∀ j (σ : S₁), ∃ (n : (ℍ[ℚ, a₂, b₂])ˣ) (t : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion),
        n ∈ Subgroup.normalizer ((Γ₁ j : Subgroup (ℍ[ℚ, a₂, b₂])ˣ) : Set (ℍ[ℚ, a₂, b₂])ˣ) ∧
        ∀ y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)),
          ((galFC₁ j σ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ t) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧

      (∀ j (σ : S₁), ∃ n : (ℍ[ℚ, a₂, b₂])ˣ,
        n ∈ Subgroup.normalizer ((Γ₁ j : Subgroup (ℍ[ℚ, a₂, b₂])ˣ) : Set (ℍ[ℚ, a₂, b₂])ˣ) ∧ (sgn₁ σ = 1 ↔ Even (padicValRat q' (nrd (n : ℍ[ℚ, a₂, b₂])))) ∧
        ∀ y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j)),
          ((galFC₁ j σ • y : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j))) : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ (scalar₁ σ))) (y : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) = 1 → sgn₁ (ιS₁ τ) = 1) ∧
      (∀ τ : ↥(A₁.decompositionSubgroup ℚ), χS₁ (ιS₁ τ) ≠ 1 → sgn₁ (ιS₁ τ) = sgn₁ σ₀₁) ∧
      sgn₁ σ₀₁ = -1 ∧ sgn₁ σ₁₁ = 1 ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₁)
        (φC : ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ (HeckeTower.cod α))) →ₐ[A₁.valuation.Completion] ↥(Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ (HeckeTower.dom α)))),
        (∀ x, (φC x : FractionRing (Omega.HolRingOf ϖ₁ ρ₁)) = (if α.2 = 0 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else s₁ α.1) • (x : FractionRing (Omega.HolRingOf ϖ₁ ρ₁))) →
        ∀ x, galFC₁ (HeckeTower.dom α) σ • φC x = φC (galFC₁ (HeckeTower.cod α) σ • x)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_one_zero.solution
