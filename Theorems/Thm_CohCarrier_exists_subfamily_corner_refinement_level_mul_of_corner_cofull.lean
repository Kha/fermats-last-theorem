import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_subfamily_corner_refinement_level_mul_of_corner_cofull
attribute [-instance] Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open Polynomial IsLocalRing CohCarrier IharaLemma IharaTower

theorem CohCarrier.exists_subfamily_corner_refinement_level_mul_of_corner_cofull
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (hord : (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (N : ℕ) [NeZero N] [NeZero (N * p)] (hpN : ¬ p ∣ N) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
        (Smin : Finset ℕ) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (hNmin : ∀ q ∈ Smin, q ≠ p → q ∣ N)
    (hNunr : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ Smin → q ∣ N → q ^ 2 ∣ N)
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    (r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r) (hrS : r ∉ S) (hrN : ¬ r ∣ N * p) (hr1 : ¬ p ∣ r - 1)

    (hrρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
        LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : ResidueField 𝒪) + 1) ^ 2)
    [Fact (CuspForm.HasIntegralStructure (N * p) 2)]
    (θ₁ : CuspForm.heckeAlgebra (N * p) 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N * p) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₀ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (πT₀ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀ →ₐ[𝒪] 𝒪)
    (πT₁ : CuspForm.heckeLocal (N * p) (↑S : Set ℕ) 𝒪 θ₁ →ₐ[𝒪] 𝒪)
    (hπ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓ₁ : ¬ ℓ ∣ N * p) (hℓ₀ : ¬ ℓ ∣ N),
      πT₁ (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (CuspForm.heckeAlgebra.T hℓ hℓ₁ hℓS)) =
        πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓ₀ hℓS)))
    (H₀ : Subgroup (ZMod (N * r))ˣ) [NeZero (N * r)]
    (hH₀ : ∀ v : (ZMod (N * r))ˣ, v ∈ H₀ ↔ ZMod.castHom (dvd_mul_left r N) (ZMod r) (v : ZMod (N * r)) = 1)

    {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 (N * r) H₀ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 (N * r) H₀ 𝒪)]
    (S₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin S₀.n)
    (e₀ : S₀.CornerRing i₀ ≃ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))]
    (tp : S₀.CornerRing i₀)
    (hT₀ : ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓr : ¬ ℓ ∣ N * r)
        (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))),
      ((e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m
          : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ ℓ 𝒪 (m : H1 (N * r) H₀ 𝒪))
    (htp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; IsUnit tp ∧ (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      ((tp • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ p 𝒪 (m : H1 (N * r) H₀ 𝒪)) ∧
      (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      ((tp • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeTlower (N * r) H₀ p 𝒪 (m : H1 (N * r) H₀ 𝒪)))
    (hocc₀ : Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)) ↑(RingHom.ker (πT₀.comp e₀.toAlgHom)) ≠ ⊥)
    (hrk₀ : Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)) =
      Module.finrank 𝒪 (Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
        ↑(RingHom.ker (πT₀.comp e₀.toAlgHom))) * Module.finrank 𝒪 (S₀.CornerRing i₀))
    (hgen : ∀ t : 𝕋₀, ∃ f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily (N * r) H₀ (↑S : Set ℕ) 𝒪)),
      ∀ m : H1 (N * r) H₀ 𝒪, t • m = f m)
    (tfull : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝕋₀)
    (htfull : ∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      ∀ m : H1 (N * r) H₀ 𝒪, tfull g • m = CohCarrier.opFamily (N * r) H₀ (↑S : Set ℕ) 𝒪 g m)
    (cfull : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝒪)
    (hcfull : ∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      tfull g - algebraMap 𝒪 𝕋₀ (cfull g) ∈ S₀.𝔪 i₀)
    (hcofull : ∀ v : H1 (N * r) H₀ 𝒪, (∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋₀ (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r) H₀ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
    (hfaith₀ : ∀ t : S₀.CornerRing i₀, (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), t • m = 0) → t = 0)

    (hdia : ∀ (σ : ↥(CongruenceSubgroup.Gamma0 (N * r))) (v : H1 (N * r) H₀ 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀) → diamondRaw (N * r) H₀ 𝒪 σ v = v)

    (αt : S₀.CornerRing i₀)
    (hαt : IsUnit αt ∧ αt * αt - tp * αt + algebraMap 𝒪 (S₀.CornerRing i₀) (p : 𝒪) = 0 ∧
      αt - tp ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 (S₀.CornerRing i₀))) :
    ∃ (_ : NeZero (N * r * p)) (H : Subgroup (ZMod (N * r * p))ˣ)
      (_ : H = H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p)))
      (𝕋ₐ 𝕋₁ : Type) (_ : CommRing 𝕋ₐ) (_ : CommRing 𝕋₁) (_ : Algebra 𝒪 𝕋ₐ) (_ : Algebra 𝒪 𝕋₁)
      (_ : Module 𝕋ₐ (H1 (N * r * p) H 𝒪)) (_ : Module 𝕋₁ (H1 (N * r * p) H 𝒪))
      (_ : IsScalarTower 𝒪 𝕋ₐ (H1 (N * r * p) H 𝒪)) (_ : IsScalarTower 𝒪 𝕋₁ (H1 (N * r * p) H 𝒪))
      (_ : Module.Finite 𝒪 𝕋ₐ) (_ : Module.Finite 𝒪 𝕋₁)
      (ι : 𝕋ₐ →ₐ[𝒪] 𝕋₁) (_ : ∀ (t : 𝕋ₐ) (v : H1 (N * r * p) H 𝒪), ι t • v = t • v)
      (U : 𝕋₁) (_ : ∀ v : H1 (N * r * p) H 𝒪, U • v = heckeT (N * r * p) H p 𝒪 v)
      (_ : Algebra.adjoin 𝒪 (Set.range ι ∪ {U}) = ⊤)
      (Sₐ : IdempotentSplitting 𝕋ₐ) (iₐ : Fin Sₐ.n) (S₁ : IdempotentSplitting 𝕋₁) (i₁ : Fin S₁.n)
      (_ : Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ)))
      (_ : Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ)))
      (_ : Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)))
      (_ : Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)))

      (h₁ₐ : LevelLE (N * r * p) (N * r * p) ⊤ H 1)
      (tA : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝕋ₐ) (dA : (ZMod (N * r * p))ˣ → 𝕋ₐ),

      (∀ g : CohCarrier.Gen (N * r) (↑S : Set ℕ), (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False) →
        ∀ v : H1 (N * r * p) H 𝒪, tA g • v = (match g with
            | .T ℓ hℓ _ _ => (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT (N * r * p) H ℓ 𝒪 v)
            | .U q hq _ => (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeT (N * r * p) H q 𝒪 v)
            | .dia _ => v)) ∧
      (∀ g : CohCarrier.Gen (N * r) (↑S : Set ℕ), (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False) →
        tA g - algebraMap 𝒪 𝕋ₐ (cfull g) ∈ Sₐ.𝔪 iₐ) ∧
      (∀ (d : (ZMod (N * r * p))ˣ) (v : H1 (N * r * p) H 𝒪), dA d • v = diamondL (N * r * p) H 𝒪 d v) ∧
      (∀ d : (ZMod (N * r * p))ˣ, dA d - 1 ∈ Sₐ.𝔪 iₐ) ∧
      Algebra.adjoin 𝒪 (tA '' {g | (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False)} ∪ Set.range dA) = ⊤ ∧

      (S₁.𝔪 i₁).comap ι = Sₐ.𝔪 iₐ ∧ U ∉ S₁.𝔪 i₁ ∧

      (∀ a : 𝒪, αt - algebraMap 𝒪 (S₀.CornerRing i₀) a ∈ IsLocalRing.maximalIdeal (S₀.CornerRing i₀) →
        U - algebraMap 𝒪 𝕋₁ a ∈ S₁.𝔪 i₁) ∧
      (∀ v : H1 (N * r * p) H 𝒪, v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁) →
        v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ)) ∧

      cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ) ≠ ⊥ ∧
      cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁) ≠ ⊥ ∧

      (∀ t : 𝕋ₐ, (∀ v : H1 (N * r * p) H 𝒪, t • v = 0) → t = 0) ∧
      (∀ t : 𝕋₁, (∀ v : H1 (N * r * p) H 𝒪, t • v = 0) → t = 0) ∧
      (∀ x : S₁.CornerRing i₁,
        (∀ m : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)), x • m = 0) → x = 0) ∧

      (∃ (tfull₁ : CohCarrier.Gen (N * r * p) (↑S : Set ℕ) → 𝕋₁) (cfull₁ : CohCarrier.Gen (N * r * p) (↑S : Set ℕ) → 𝒪),

        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ N * r * p) (hℓM : ¬ ℓ ∣ N * r),
          tfull₁ (.T ℓ hℓ hℓS hℓL) = ι (tA (.T ℓ hℓ hℓS hℓM)) ∧ cfull₁ (.T ℓ hℓ hℓS hℓL) = cfull (.T ℓ hℓ hℓS hℓM)) ∧
        (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p) (hqM : q ∣ N * r), q ∣ N →
          tfull₁ (.U q hq hqL) = ι (tA (.U q hq hqM)) ∧ cfull₁ (.U q hq hqL) = cfull (.U q hq hqM)) ∧
        (∀ (hpL : p ∣ N * r * p), tfull₁ (.U p Fact.out hpL) = U ∧
          αt - algebraMap 𝒪 (S₀.CornerRing i₀) (cfull₁ (.U p Fact.out hpL)) ∈
            IsLocalRing.maximalIdeal (S₀.CornerRing i₀)) ∧
        (∀ d : (ZMod (N * r * p))ˣ, tfull₁ (.dia d) = ι (dA d) ∧ cfull₁ (.dia d) = 1) ∧

        (∀ x : 𝕋₁, ∃ f ∈ Algebra.adjoin 𝒪
            (CohCarrier.opFamily (N * r * p) H (↑S : Set ℕ) 𝒪 '' {g | (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p)}),
          ∀ v : H1 (N * r * p) H 𝒪, x • v = f v) ∧

        (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
          ∀ v : H1 (N * r * p) H 𝒪, tfull₁ g • v = CohCarrier.opFamily (N * r * p) H (↑S : Set ℕ) 𝒪 g v) ∧
        (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
          tfull₁ g - algebraMap 𝒪 𝕋₁ (cfull₁ g) ∈ S₁.𝔪 i₁) ∧

        (∀ v : H1 (N * r * p) H 𝒪, (∀ g, (∀ (q : ℕ) (hq : q.Prime) (hqL : q ∣ N * r * p), g = CohCarrier.Gen.U q hq hqL → q ∣ N * p) →
          ∀ k : ℕ, ∃ n : ℕ, ((tfull₁ g - algebraMap 𝒪 𝕋₁ (cfull₁ g)) ^ n) • v ∈
            ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r * p) H 𝒪))) →
          v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_subfamily_corner_refinement_level_mul_of_corner_cofull.solution
