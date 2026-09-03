import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP
attribute [-simp] PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    [IsDiscreteValuationRing ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)]

    {h : ℕ} (𝒢D : PDivisibleGroup ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) p h)
    (ΔD : 𝒢D.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔDinj : Function.Injective ΔD)
    (hΔDlev : ∀ (v : ℕ) (x : ModularCurve.JH M H),
      (∃ y : 𝒢D.Point (AlgebraicClosure ℚ) v, ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = x) ↔ x ∈ O.finPts (p ^ v))
    (hΔDgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → ∀ z : 𝒢D.Points (AlgebraicClosure ℚ), ΔD (τ' • z) = τ • ΔD z)
    (htorD : ∀ v : ℕ, O.toricPts (p ^ v) ≤ O.finPts (p ^ v))

    (ρD : ModularCurve.XHDRLevel.R p →+* (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)))
    (ιD : ∀ v : ℕ, Spec (CommRingCat.of (𝒢D.level v)) ⟶ O.G)
    (hρD : (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (AlgebraicClosure ℚ)).comp ρD = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιDbase : ∀ v : ℕ, ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD))
    (hιDcl : ∀ (v : ℕ) (h1 : ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρD)) (ιD v)
        (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v)))) h1))
    (hιDp : ∀ v : ℕ, ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιDmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B] (x y : 𝒢D.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιDt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢D.transition v : 𝒢D.level (v + 1) →+* 𝒢D.level v)) ≫ ιD (v + 1) = ιD v)
    (hιDfin : ∀ (v : ℕ)
      (h3 : ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρD))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρD))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρD))).base x = IsLocalRing.closedPoint (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) →
          x ∈ Set.range jv.base)

    (hιDpts : ∀ (v : ℕ) (x : 𝒢D.Point (AlgebraicClosure ℚ) v),
      (O.pts (ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] (AlgebraicClosure ℚ)) : 𝒢D.level v →+* (AlgebraicClosure ℚ))) ≫ ιD v)

    [Algebra ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (ZMod p)]
    (hresD : ∀ x : ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring), algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))

    (C : ℕ → Type) [∀ v, CommRing (C v)] [∀ v, HopfAlgebra ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C v)]
    [∀ v, Coalgebra.IsCocomm ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C v)] [∀ v, Module.Finite ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C v)] [∀ v, Module.Free ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C v)]
    (π : ∀ v : ℕ, 𝒢D.level v →ₐc[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v)
    (hπ : ∀ v, Function.Surjective (π v))
    (hπpts : ∀ (v : ℕ) (x : 𝒢D.Point (AlgebraicClosure ℚ) v),
      (∃ χ : C v →ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] AlgebraicClosure ℚ, χ.comp (π v : 𝒢D.level v →ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v) = PDivisibleGroup.Point.toAlgHom x) ↔
      ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
    :

    (∀ v : ℕ, ∃ Ver : ZMod p ⊗[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v ≃ₐc[ZMod p] ZMod p ⊗[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v,
      ∀ χ : CartierDual (ZMod p) (ZMod p ⊗[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v), CartierDual.map (Ver : ZMod p ⊗[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v →ₐc[ZMod p] ZMod p ⊗[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v) χ = χ ^ p) ∧

    (∀ (v : ℕ) (χ : C v →ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] AlgebraicClosure ℚ) (c : C v),
      Pl.valuation (χ c - algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1) ∧

    (∃ tC : ∀ v : ℕ, C (v + 1) →ₐc[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] C v,
      (∀ v, Function.Surjective (tC v)) ∧
      (∀ v : ℕ, (tC v).comp (π (v + 1)) = (π v).comp (𝒢D.transition v)) ∧
      (∀ v, RingHom.ker (tC v) = PDivisibleGroup.Hopf.torsionIdeal ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C (v + 1)) (p ^ v)) ∧
      (∀ v, Module.finrank ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (C v) = p ^ (v * O.toricRank))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP.solution
