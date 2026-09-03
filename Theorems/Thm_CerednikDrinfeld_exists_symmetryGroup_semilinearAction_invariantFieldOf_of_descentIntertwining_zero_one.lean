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
import P2M.Sol.S_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_zero_one
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

theorem CerednikDrinfeld.exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_zero_one

    {a₁ b₁ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₁ : IsDefiniteRamifiedExactlyAt a₁ b₁ q')
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ q)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * q))
    (hnorm₁ : Submodule.conjByFiniteIdele (meetOrder R₁ n₁) n₁ = meetOrder R₁ n₁)
    (hsq₁ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)),
      classSetShift _ n₁ (classSetShift _ n₁ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    (hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁)

    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)

    (FN : Type) [Field FN] [Algebra (AlgebraicClosure ℚ) FN] [IsCurveOver (AlgebraicClosure ℚ) FN]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) FN]
    (𝕋 : HeckeTower.TowerData q q' FN)
    (hfg : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))
    (galN : ↥(A₂.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) FN)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A₂.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (hgalN : ∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galN τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (hgalT : ∀ ℓ (τ : ↥(A₂.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galT ℓ τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) FN) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

    [hiso₂ : Fact (A₂.DecompositionIsometric ℚ)]
    (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : ((q : ℕ) : 𝓞 ℚ) ∈ v₂.asIdeal)

    (ι₂ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) (hι₂ : Function.Injective ι₂)
    (ρ₂ : (ℍ[ℚ, a₁, b₁])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₂)))
    (hρ₂ : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, ρ₂ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₂ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₂)) x))

    (ϖ₂ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
    (hϖ₂ : algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion ϖ₂.ϖ = ((q : AlgebraicClosure ℚ) : A₂.valuation.Completion))
    [hdom₂ : IsDomain (Omega.HolRingOf ϖ₂ ρ₂)]

    (s₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf₂ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₂ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₂ ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf₂ ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₂ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s₂ ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₂ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓ₂0 : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γ₂ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ Even (padicValRat q (nrd (x : ℍ[ℚ, a₁, b₁]))))
    (hΓ₂ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₂ (some ℓ) = Γ₂ none ⊓ (Γ₂ none).map (MulAut.conj (s₂ ℓ)).toMonoidHom)

    (w₂ wbar₂ : HeckeTower.Obj q q' → (ℍ[ℚ, a₁, b₁])ˣ)
    (hw₂ : (w₂ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v₂ ∧ nrd (w₂ none : ℍ[ℚ, a₁, b₁]) = (q : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₂ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₁ (sf₂ ℓ)) v₂ ∧ nrd (w₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q : ℚ))
    (hwbar₂ :
      (nrd (wbar₂ none : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₂ none) ∈ Submodule.localBoxUnits R₁ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox R₁ u ↔
            x ∈ Submodule.localBox R₁ u) ∧
          ((((CosetGraph.toLoc u (wbar₂ none))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
              ((CosetGraph.toLoc u (wbar₂ none) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
            x ∈ Submodule.localBox Λ₁ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₂ (some ℓ) : ℍ[ℚ, a₁, b₁]) = (q' : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₂ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₁ (sf₂ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₂ → ∀ x : CosetGraph.Loc a₁ b₁ u,
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₁ (sf₂ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₂ (some ℓ)))⁻¹ : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) * x *
                ((CosetGraph.toLoc u (wbar₂ (some ℓ)) : (CosetGraph.Loc a₁ b₁ u)ˣ) : CosetGraph.Loc a₁ b₁ u) ∈ Submodule.localBox Λ₁ u ↔
              x ∈ Submodule.localBox Λ₁ u))))

    (dIso₂ : ↥(A₂.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion)
    (hdIso₂ : ∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (x : A₂.valuation.Completion), (dIso₂ τ).toRingEquiv x = τ • x)

    (χ₂ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (ιM₂ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₂ ρ₂))
    (hI : CerednikDrinfeld.DescentIntertwining q (0 : Fin 2) (1 : Fin 2) A₂ ρ₂ ϖ₂ Γ₂ w₂ wbar₂ s₂ dIso₂
      FN 𝕋 galN galT W WT χ₂ ιM₂) :
    ∃ (S₂ : Type) (_ : Group S₂) (scalar₂ : S₂ →* ↥(A₂.decompositionSubgroup ℚ))
      (ιS₂ : ↥(A₂.decompositionSubgroup ℚ) →* S₂) (_ : ∀ τ, scalar₂ (ιS₂ τ) = τ)

      (σ₀₂ σ₁₂ : S₂)
      (χS₂ : S₂ →* Multiplicative (ZMod 2))

      (galF₂ : ∀ j : HeckeTower.Obj q q', S₂ →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.objField j))

      (galFC₂ : ∀ j : HeckeTower.Obj q q',
        S₂ →* SemilinearAut A₂.valuation.Completion ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j)))

      (sgn₂ : S₂ →* ℤˣ),

      (∀ σ : S₂, ∃ (τ : ↥(A₂.decompositionSubgroup ℚ)) (u v : ℕ), σ = ιS₂ τ * σ₀₂ ^ u * σ₁₂ ^ v) ∧
      scalar₂ σ₀₂ = 1 ∧ scalar₂ σ₁₂ = 1 ∧ σ₀₂ * σ₀₂ = 1 ∧ σ₁₂ * σ₁₂ = 1 ∧
      σ₀₂ * σ₁₂ = σ₁₂ * σ₀₂ ∧ (∀ τ, ιS₂ τ * σ₀₂ = σ₀₂ * ιS₂ τ) ∧ (∀ τ, ιS₂ τ * σ₁₂ = σ₁₂ * ιS₂ τ) ∧

      (∀ (H : Type) [Group H] (f : ↥(A₂.decompositionSubgroup ℚ) →* H) (h₀ h₁ : H),
        h₀ * h₀ = 1 → h₁ * h₁ = 1 → h₀ * h₁ = h₁ * h₀ → (∀ τ, f τ * h₀ = h₀ * f τ) → (∀ τ, f τ * h₁ = h₁ * f τ) →
        ∃ F : S₂ →* H, (∀ τ, F (ιS₂ τ) = f τ) ∧ F σ₀₂ = h₀ ∧ F σ₁₂ = h₁) ∧

      (∀ j (σ : S₂) (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (galF₂ j σ) a =
        ((scalar₂ σ : ↥(A₂.decompositionSubgroup ℚ)) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a) ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ), galF₂ none (ιS₂ τ) = galN τ) ∧
      (∀ (ℓ : HeckeTower.AwayPrime q q') (τ : ↥(A₂.decompositionSubgroup ℚ)), galF₂ (some ℓ) (ιS₂ τ) = galT ℓ τ) ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₂) (x : 𝕋.objField (HeckeTower.cod α)),
        galF₂ (HeckeTower.dom α) σ • (show 𝕋.objField (HeckeTower.dom α) from 𝕋.φ α x) =
          (show 𝕋.objField (HeckeTower.dom α) from 𝕋.φ α (galF₂ (HeckeTower.cod α) σ • x))) ∧
      galF₂ none σ₀₂ = W 0 ∧ galF₂ none σ₁₂ = W 1 ∧
      (∀ ℓ : HeckeTower.AwayPrime q q', galF₂ (some ℓ) σ₀₂ = WT ℓ 0 ∧ galF₂ (some ℓ) σ₁₂ = WT ℓ 1) ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ), χS₂ (ιS₂ τ) = χ₂ τ) ∧ χS₂ σ₀₂ ≠ 1 ∧ χS₂ σ₁₂ = 1 ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ),
        (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₂.inertiaSubgroupIn ℚ → χS₂ (ιS₂ τ) = 1) ∧
      (∀ φ : ↥(A₂.decompositionSubgroup ℚ),
        A₂.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q → χS₂ (ιS₂ φ) ≠ 1) ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ), χS₂ (ιS₂ τ) = 1 ↔
        ∀ x : IsLocalRing.ResidueField ↥A₂, x ^ (q ^ 2) = x → τ • x = x) ∧

      (∀ j (σ : S₂) (c : A₂.valuation.Completion),
        SemilinearAut.baseAut (galFC₂ j σ) c = (scalar₂ σ) • c) ∧
      (∀ j (σ : S₂) (c : A₂.valuation.Completion),
        SemilinearAut.baseAut (galFC₂ j σ) c = (dIso₂ (scalar₂ σ)).toRingEquiv c) ∧
      (∀ j (c : A₂.valuation.Completion), SemilinearAut.baseAut (galFC₂ j σ₀₂) c = c) ∧
      (∀ j (c : A₂.valuation.Completion), SemilinearAut.baseAut (galFC₂ j σ₁₂) c = c) ∧
      (∀ j (σ : S₂) (x : 𝕋.objField j) (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))),
        (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = ιM₂ j x →
          ((galFC₂ j σ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = ιM₂ j (galF₂ j σ • x)) ∧
      (∀ j (τ : ↥(A₂.decompositionSubgroup ℚ)) (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))),
        ((galFC₂ j (ιS₂ τ) • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
          (if χ₂ τ = 1 then (1 : (ℍ[ℚ, a₁, b₁])ˣ) else w₂ j) •
            Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ (dIso₂ τ)) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧
      (∀ j (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))),
        ((galFC₂ j σ₀₂ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = (w₂ j) • (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧
      (∀ j (y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))),
        ((galFC₂ j σ₁₂ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = (wbar₂ j) • (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧

      (∀ j (σ : S₂), ∃ (n : (ℍ[ℚ, a₁, b₁])ˣ) (t : Omega.IsometricAut ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion),
        n ∈ Subgroup.normalizer ((Γ₂ j : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) : Set (ℍ[ℚ, a₁, b₁])ˣ) ∧
        ∀ y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j)),
          ((galFC₂ j σ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ t) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧

      (∀ j (σ : S₂), ∃ n : (ℍ[ℚ, a₁, b₁])ˣ,
        n ∈ Subgroup.normalizer ((Γ₂ j : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) : Set (ℍ[ℚ, a₁, b₁])ˣ) ∧ (sgn₂ σ = 1 ↔ Even (padicValRat q (nrd (n : ℍ[ℚ, a₁, b₁])))) ∧
        ∀ y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j)),
          ((galFC₂ j σ • y : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ j))) : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) =
            n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₂ ρ₂ (dIso₂ (scalar₂ σ))) (y : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ), χS₂ (ιS₂ τ) = 1 → sgn₂ (ιS₂ τ) = 1) ∧
      (∀ τ : ↥(A₂.decompositionSubgroup ℚ), χS₂ (ιS₂ τ) ≠ 1 → sgn₂ (ιS₂ τ) = sgn₂ σ₀₂) ∧
      sgn₂ σ₀₂ = -1 ∧ sgn₂ σ₁₂ = 1 ∧
      (∀ (α : HeckeTower.Arr q q') (σ : S₂)
        (φC : ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ (HeckeTower.cod α))) →ₐ[A₂.valuation.Completion] ↥(Mumford.invariantFieldOf A₂.valuation.Completion (ℍ[ℚ, a₁, b₁])ˣ (Omega.HolRingOf ϖ₂ ρ₂) (Γ₂ (HeckeTower.dom α)))),
        (∀ x, (φC x : FractionRing (Omega.HolRingOf ϖ₂ ρ₂)) = (if α.2 = 0 then (1 : (ℍ[ℚ, a₁, b₁])ˣ) else s₂ α.1) • (x : FractionRing (Omega.HolRingOf ϖ₂ ρ₂))) →
        ∀ x, galFC₂ (HeckeTower.dom α) σ • φC x = φC (galFC₂ (HeckeTower.cod α) σ • x)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_symmetryGroup_semilinearAction_invariantFieldOf_of_descentIntertwining_zero_one.solution
