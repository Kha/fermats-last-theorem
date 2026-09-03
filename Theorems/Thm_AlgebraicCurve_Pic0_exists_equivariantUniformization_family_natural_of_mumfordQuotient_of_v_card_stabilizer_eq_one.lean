import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one
import Definitions.Def_Compat_Mathlib430
attribute [-instance] Valuation.algebraCompletion Valuation.uniformContinuousConstSMul_withVal Valuation.continuousConstSMul_withVal AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] Valuation.algebraMap_completion_apply ValuationSubring.ratCast_mem_ratClosure ValuationSubring.intCast_mem_ratClosure ValuationSubring.natCast_mem_ratClosure CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq LocalGL2.swapUnit_val CerednikDrinfeld.Omega.coordSub_apply CerednikDrinfeld.Omega.coord_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve

theorem AlgebraicCurve.Pic0.exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)

    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (hϖr : Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ) = Valued.v ((r : ℕ) : A.valuation.Completion))

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]
    [DecidablePred (· ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))]

    (J : Type) (Γ : J → Subgroup G)
    (htp : ∀ j, (Γ j).map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [∀ j, Mumford.GraphAction ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ (j : J) (d : (BruhatTits.tree R₀ K₀).Dart), Finite (MulAction.stabilizer (↥((Γ j).map ρ)) d))

    (htame : ∀ (j : J) (w : LT.LatticeTree.Vertex R₀ K₀),
      Valued.v ((Nat.card ↥(MulAction.stabilizer ↥((Γ j).map ρ) w) : ℕ) : A.valuation.Completion) = 1)

    (FC : J → Type) [∀ j, Field (FC j)] [∀ j, Algebra A.valuation.Completion (FC j)] [hcurve : ∀ j, IsCurveOver A.valuation.Completion (FC j)]
    (eFC : ∀ j, FC j ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j)))
    (hfg : ∀ j, ∃ x : FC j, Transcendental A.valuation.Completion x ∧
      FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set (FC j))) (FC j))

    (E V : J → Type) [∀ j, Fintype (E j)] [∀ j, Fintype (V j)] [∀ j, DecidableEq (E j)] [∀ j, DecidableEq (V j)]
    (D : ∀ j, DegeneracyData (E j) (V j))
    (eV : ∀ j, Mumford.QuotVert ↥((Γ j).map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V j)

    (eE : ∀ j, {e : Mumford.QuotEdge ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E j)
    (hDa : ∀ j (e : {e : Mumford.QuotEdge ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}), (D j).a (eE j e) = eV j (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ j (e : {e : Mumford.QuotEdge ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}), (D j).b (eE j e) = eV j (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ j (e : {e : Mumford.QuotEdge ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}), ((D j).w (eE j e) : ℕ) = Nat.card (MulAction.stabilizer (↥((Γ j).map ρ)) e.1.out))

    (galFC : ∀ j, S →* SemilinearAut A.valuation.Completion (FC j))
    (hgalFC_base : ∀ j (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC j σ) c = (scalar σ) • c)

    (hgal : ∀ j (σ : S), ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ j : Subgroup G) : Set G) ∧ (∀ y : FC j, ((eFC j (galFC j σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC j y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ))))

    (πV : ∀ j, S →* Equiv.Perm (V j)) (πE : ∀ j, S →* Equiv.Perm (E j)) (sgn : S →* ℤˣ)
    (hπV : ∀ j (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ j : Subgroup G) : Set G) →
      (∀ y : FC j, ((eFC j (galFC j σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC j y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ v : LT.LatticeTree.Vertex R₀ K₀, πV j σ (eV j (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV j (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (ρ n • v)))
    (hπE : ∀ j (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ j : Subgroup G) : Set G) →
      (∀ y : FC j, ((eFC j (galFC j σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC j y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ j))) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ e : {e : Mumford.QuotEdge ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = 1 ∧ ((eE j).symm (πE j σ (eE j e))).1 = (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = -1 ∧ ((eE j).symm (πE j σ (eE j e))).1 = (Quotient.mk (MulAction.orbitRel ↥((Γ j).map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (hπ_width : ∀ j σ e, (D j).w (πE j σ e) = (D j).w e)
    (hsgn_pos : ∀ j σ e, sgn σ = 1 → (D j).a (πE j σ e) = πV j σ ((D j).a e) ∧ (D j).b (πE j σ e) = πV j σ ((D j).b e))
    (hsgn_neg : ∀ j σ e, sgn σ = -1 → (D j).a (πE j σ e) = πV j σ ((D j).b e) ∧ (D j).b (πE j σ e) = πV j σ ((D j).a e))
    (hπ_inertia : ∀ j (τ : ↥(A.decompositionSubgroup ℚ)),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        πV j (ι τ) = 1 ∧ πE j (ι τ) = 1 ∧ sgn (ι τ) = 1)
    (actZ : ∀ j, S →* (↥(ribbonKernel (D j)) ≃ₗ[ℤ] ↥(ribbonKernel (D j))))
    (hactZ : ∀ j (σ : S) (x : ↥(ribbonKernel (D j))) (e : E j),
      (actZ j σ x : E j → ℤ) (πE j σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E j → ℤ) e)

    (Arr : Type) (dom cod : Arr → J) (g : Arr → G) (hg : ∀ α, ρ (g α) ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    (hArr : ∀ α, Γ (dom α) ≤ (Γ (cod α)).map (MulAut.conj (g α)).toMonoidHom)

    (φ : ∀ α, (FC (cod α)) →ₐ[A.valuation.Completion] (FC (dom α)))
    (hφ : ∀ α (x : FC (cod α)),
      ((eFC (dom α) (φ α x) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ (dom α)))) : FractionRing (Omega.HolRingOf ϖ ρ)) = (g α) • ((eFC (cod α) x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) (Γ (cod α)))) : FractionRing (Omega.HolRingOf ϖ ρ)))
    (hφC : ∀ α, (φ α).toRingHom.IsIntegral)
    (hfinC : ∀ α, FiniteAlong A.valuation.Completion (φ α)) (hsepC : ∀ α, SeparableAlong A.valuation.Completion (φ α))
    (hgalC_arr : ∀ α (σ : S) (x : (FC (cod α))), galFC (dom α) σ • φ α x = φ α (galFC (cod α) σ • x))

    (μ : ∀ α, (D (dom α)).FiniteHom (D (cod α)))
    (hμV : ∀ α (v : LT.LatticeTree.Vertex R₀ K₀), (μ α).mapV (eV (dom α) (Quotient.mk (MulAction.orbitRel ↥((Γ (dom α)).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV (cod α) (Quotient.mk (MulAction.orbitRel ↥((Γ (cod α)).map ρ) (LT.LatticeTree.Vertex R₀ K₀)) ((ρ (g α))⁻¹ • v)))
    (hμE : ∀ α (e : {e : Mumford.QuotEdge ↥((Γ (dom α)).map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}),
      ((eE (cod α)).symm ((μ α).mapE (eE (dom α) e))).1 = (Quotient.mk (MulAction.orbitRel ↥((Γ (cod α)).map ρ) (BruhatTits.tree R₀ K₀).Dart) ((ρ (g α))⁻¹ • e.1.out)))
    (hdeg : ∀ α, ((μ α).degTotal : ℕ) = finrankAlong A.valuation.Completion (φ α))
    (hμ_equiv : ∀ α (σ : S) (e : E (dom α)), (μ α).mapE (πE (dom α) σ e) = πE (cod α) σ ((μ α).mapE e)) :
    ∃ 𝒰 : ∀ j, EquivariantUniformization r (D j) A hA (Pic0 A.valuation.Completion (FC j))
        S scalar (actZ j)
        ((DistribMulAction.toAddAut' (SemilinearAut A.valuation.Completion (FC j)) (Pic0 A.valuation.Completion (FC j))).comp (galFC j)),

      (∀ j (z : Pic0 A.valuation.Completion (FC j)),
        (∀ τ : ↥(A.decompositionSubgroup ℚ),
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → galFC j (ι τ) • z = z) →
        ∃ u : (𝒰 j).P.TorusPoints,
          (∀ τ : ↥(A.decompositionSubgroup ℚ),
            (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
            ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = τ • c) →
              (𝒰 j).P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u) ∧
          (𝒰 j).eFull u = z) ∧

      (∀ α (u : (𝒰 (cod α)).P.TorusPoints)
          (D₁ : Divisor.degZero (K := A.valuation.Completion) (F := (FC (cod α))))
          (D₁' : Divisor.degZero (K := A.valuation.Completion) (F := (FC (dom α)))),
        (𝒰 (cod α)).eFull u = Pic0.mk D₁ →
        (D₁' : Divisor A.valuation.Completion (FC (dom α))) = Divisor.pullbackAlong (φ α) (hφC α) (D₁ : Divisor A.valuation.Completion (FC (cod α))) →
        (𝒰 (dom α)).eFull (u.comp (μ α).pushforward) = Pic0.mk D₁') ∧

      (∀ α (u' : (𝒰 (dom α)).P.TorusPoints)
          (D₁' : Divisor.degZero (K := A.valuation.Completion) (F := (FC (dom α))))
          (D₁ : Divisor.degZero (K := A.valuation.Completion) (F := (FC (cod α)))),
        (𝒰 (dom α)).eFull u' = Pic0.mk D₁' →
        (D₁ : Divisor A.valuation.Completion (FC (cod α))) = Divisor.pushforwardAlong (φ α) (hφC α) (D₁' : Divisor A.valuation.Completion (FC (dom α))) →
        (𝒰 (cod α)).eFull (u'.comp (μ α).pullback) = Pic0.mk D₁) ∧

      (∀ α (x : ↥(ribbonKernel (D (cod α)))) (y : ↥(ribbonKernel (D (dom α)))),
        ((((Additive.toMul ((𝒰 (dom α)).P.Q ((μ α).pullback x) y)) : (↥(𝒰 (dom α)).K)ˣ) : ↥(𝒰 (dom α)).K) : A.valuation.Completion) =
          ((((Additive.toMul ((𝒰 (cod α)).P.Q x ((μ α).pushforward y))) : (↥(𝒰 (cod α)).K)ˣ) : ↥(𝒰 (cod α)).K) : A.valuation.Completion)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_equivariantUniformization_family_natural_of_mumfordQuotient_of_v_card_stabilizer_eq_one.solution
