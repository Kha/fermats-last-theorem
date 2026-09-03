import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_klevel_smoothPointStalks_of_baseSmoothPointStalks_of_eq_two_of_dvd_chart
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.klevel_smoothPointStalks_of_baseSmoothPointStalks_of_eq_two_of_dvd_chart
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    {ι : Type} (K : ι → IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKfin : ∀ n, FiniteDimensional ↥k₀ ↥(K n))
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : AlgebraicClosure ℚ) ∈ A)
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥)
    (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →
        ((∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                ∀ x : FSS,
                  ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
        ∃ (N : Finset (Place (ResidueField ↥A) FSS))
          (Sb : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
          (φb : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥Ab →+* ↥(Sb Q)))
          (χb : (Q : Place (ResidueField ↥A) FSS) → (↥(Sb Q) →+* ResidueField ↥A))
          (Db : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          N.card = q + 1 ∧

          (∃ B : Subring ↥(fieldBar q M'),
            (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers) ∧
            (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sb Q) ∧
            (∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
              ∃ (f : ↥(fieldBar q M')) (_ : f ∈ B) (hfR : f ∈ R.integers), R.residue ⟨f, hfR⟩ = z)) ∧
          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

            (
              (∀ a : ↥Ab, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ Sb Q) ∧

              (∀ a : ↥Ab, ((φb Q (Polynomial.C a) : ↥(Sb Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧
              (∀ a : ↥Ab, χb Q (φb Q (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) ∧
              χb Q (φb Q Polynomial.X) = 0 ∧

              (∃ _ : IsLocalRing ↥(Sb Q), RingHom.ker (χb Q) = maximalIdeal ↥(Sb Q)) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ Sb Q → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(Sb Q), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

              (φb Q).FormallySmooth ∧ (φb Q).FormallyUnramified ∧ (φb Q).EssFiniteType ∧

              (∃ hSR : ∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ R.integers,
                ∀ f : ↥(Sb Q), (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φb Q (Polynomial.C ϖb) ∣ f) ∧

              (∀ f : ↥(Sb Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χb Q f)) ∧

              (∃ hR : ((φb Q Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')) ∈ R.integers,
                Q.ord (R.residue ⟨((φb Q Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

              (∀ P, P ∈ Db Q ↔ (P.IsRational ∧
                (∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
                (∀ f : ↥(Sb Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χb Q f = 0))) )) ∧

          (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Db Q → P ∈ Db Q' → Q = Q') ∧

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Db Q,
            0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
              (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
              (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Db Q) = Db (R.resAut τ hτ • Q)))) →
        (

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                ∀ x : FSS,
                  ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
        ∃ (N : Finset (Place (ResidueField ↥A) FSS))
          (Sn : Place (ResidueField ↥A) FSS → ι → Subring ↥(fieldBar q M'))
          (φn : (Q : Place (ResidueField ↥A) FSS) → (n : ι) → (Polynomial ↥(An n) →+* ↥(Sn Q n)))
          (χn : (Q : Place (ResidueField ↥A) FSS) → (n : ι) → (↥(Sn Q n) →+* ResidueField ↥A))
          (Dn : Place (ResidueField ↥A) FSS → ι → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          N.card = q + 1 ∧

          (∃ B : Subring ↥(fieldBar q M'),
            (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers) ∧
            (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ (n : ι) (f : ↥(fieldBar q M')), f ∈ B → f ∈ Sn Q n) ∧
            (∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
              ∃ (f : ↥(fieldBar q M')) (_ : f ∈ B) (hfR : f ∈ R.integers), R.residue ⟨f, hfR⟩ = z)) ∧
          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

            (∀ n : ι,

              Function.Surjective (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) ∧

              (∀ a : ↥(An n), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ) ∈ Sn Q n) ∧

              (φn Q n).FormallySmooth ∧ (φn Q n).FormallyUnramified ∧

              (∀ a : ↥(An n), ((φn Q n (Polynomial.C a) : ↥(Sn Q n)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) ∧

              (∀ a : ↥(An n), χn Q n (φn Q n (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) ∧

              χn Q n (φn Q n Polynomial.X) = 0 ∧

              (∀ c : ↥(An n), IsLocalRing.residue ↥A ⟨((c : ↥(K n)) : AlgebraicClosure ℚ), (hAn n c).mp c.2⟩ = 0 →
                ∃! χ : ↥(Sn Q n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn Q n (Polynomial.C a)) = a) ∧
                  (∀ f : ↥(Sn Q n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : AlgebraicClosure ℚ), (hAn n _).mp (χ f).2⟩ = χn Q n f) ∧
                  χ (φn Q n Polynomial.X) = c) ∧

              (∀ f : ↥(Sn Q n), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χn Q n f)) ∧

              (∃ hR : ((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')) ∈ R.integers,
                Q.ord (R.residue ⟨((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

              (∀ P, P ∈ Dn Q n ↔ (P.IsRational ∧
                (∀ f : ↥(Sn Q n), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
                (∀ f : ↥(Sn Q n), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χn Q n f = 0))) ∧

              (∀ c : ↥(An n), φn Q n Polynomial.X ≠ φn Q n (Polynomial.C c)) ∧

              (∃ (_ : IsLocalRing ↥(Sn Q n)),
                (∀ f : ↥(Sn Q n), f ∈ maximalIdeal ↥(Sn Q n) ↔ χn Q n f = 0) ∧
                IsNoetherianRing ↥(Sn Q n) ∧ UniqueFactorizationMonoid ↥(Sn Q n)) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ Sn Q n → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(Sn Q n), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

              (∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
                LinearIndependent ↥(K n) c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) ∧

              (∀ χ : ↥(Sn Q n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn Q n (Polynomial.C a)) = a) →
                (∀ f : ↥(Sn Q n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : AlgebraicClosure ℚ), (hAn n _).mp (χ f).2⟩ = χn Q n f) →
                RingHom.ker χ = Ideal.span {φn Q n Polynomial.X - φn Q n (Polynomial.C (χ (φn Q n Polynomial.X)))}) ∧

              (∃ ϖ : ↥(An n), maximalIdeal ↥(An n) = Ideal.span {ϖ} ∧ ϖ ≠ 0 ∧
                Prime (φn Q n (Polynomial.C ϖ)) ∧
                (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ →
                  (f ∈ R.integers ↔ ∃ g h : ↥(Sn Q n), ¬ (φn Q n (Polynomial.C ϖ) ∣ h) ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M')))) ∧
                (∀ p : ↥(Sn Q n), Prime p → ¬ Associated p (φn Q n (Polynomial.C ϖ)) →
                  ∀ x : ↥(Sn Q n), ∃ r : Polynomial ↥(An n), r.Monic ∧ p ∣ (r.map ((φn Q n).comp Polynomial.C)).eval x)) ∧

              (∃ G : Finset ↥(fieldBar q M'), ↑G ⊆ (Sn Q n : Set ↥(fieldBar q M')) ∧ ∀ f ∈ Sn Q n, ∃ g h : ↥(fieldBar q M'),
                g ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ∧
                h ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ∧
                (∃ u : (↥(Sn Q n))ˣ, ((u : ↥(Sn Q n)) : ↥(fieldBar q M')) = h) ∧ f * h = g)) ∧

            (∃ hmono : ∀ n n', K n ≤ K n' → Sn Q n ≤ Sn Q n',
              (∀ n n', K n ≤ K n' →
                Sn Q n' ≤ Subring.closure ((Sn Q n : Set ↥(fieldBar q M')) ∪ ((fun a : ↥(An n') => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n')) : AlgebraicClosure ℚ)) '' Set.univ))) ∧
              (∀ n n', ((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')) = ((φn Q n' Polynomial.X : ↥(Sn Q n')) : ↥(fieldBar q M'))) ∧
              (∀ n n' (h : K n ≤ K n') (f : ↥(Sn Q n)), χn Q n' ⟨(f : ↥(fieldBar q M')), hmono n n' h f.2⟩ = χn Q n f))) ∧

          (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ (n : ι) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Dn Q n → P ∈ Dn Q' n → Q = Q') ∧

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ n : ι, ∀ P ∈ Dn Q n,
            0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
              (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
              (Q ∉ N → ∀ n : ι, AlgebraicCurve.RegularProlongation.smulDisc τ (Dn Q n) = Dn (R.resAut τ hτ • Q) n))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_klevel_smoothPointStalks_of_baseSmoothPointStalks_of_eq_two_of_dvd_chart.solution
