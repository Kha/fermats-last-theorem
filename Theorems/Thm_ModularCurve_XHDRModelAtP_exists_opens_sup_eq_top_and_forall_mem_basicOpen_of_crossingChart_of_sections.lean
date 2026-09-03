import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_exists_opens_sup_eq_top_and_forall_mem_basicOpen_of_crossingChart_of_sections

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.XHDRLevel MvPolynomial
open scoped MatrixGroups

set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_opens_sup_eq_top_and_forall_mem_basicOpen_of_crossingChart_of_sections
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)))) =
      U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal ∧
        CrossingQuotient.V (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal) ↔
      U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n)
    (Wet : (U : Scheme.{0}).Opens)
    (hWet : ∃ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n ∧ y ∈ Wet)
    [AlgebraicGeometry.Etale (Wet.ι ≫ f)]

    (x' y' : ↥A) (hxy : x' * y' = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
    (x'' y'' : ↥A) (hxy' : x'' * y'' = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
    (sU sU' : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}))
    (hsU : sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _) (hsU' : sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _)

    (hsx : U.ι.base (sU.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n)
    (hsx' : U.ι.base (sU'.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n)
    (hfs : sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x' y' hxy).toRingHom))
    (hfs' : sU' ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x'' y'' hxy').toRingHom))
    (huniq : ∀ s₁ : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}), s₁ ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
      U.ι.base (s₁.base (IsLocalRing.closedPoint ↥A)) =
        (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n →
      s₁ ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x' y' hxy).toRingHom) → s₁ = sU)
    (huniq' : ∀ s₁ : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}), s₁ ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
      U.ι.base (s₁.base (IsLocalRing.closedPoint ↥A)) =
        (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n →
      s₁ ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x'' y'' hxy').toRingHom) → s₁ = sU') :
    letI Mdl : Scheme.{0} := CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e)
    letI φ : CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e) →+* Γ(Mdl, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)))).inv.hom
    letI a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A _ x')
    letI b : Γ(Mdl, ⊤) := φ (algebraMap ↥A _ y' - CrossingQuotient.V _)
    letI a' : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥A _ x'')
    letI b' : Γ(Mdl, ⊤) := φ (algebraMap ↥A _ y'' - CrossingQuotient.V _)
    ∃ W₂ W₃ : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens,
      W₂ ⊔ W₃ = ⊤ ∧ W₂ ≤ U ∧
      (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n ∈ W₂ ∧
      (∀ z, z ∈ W₃ ↔ (z ∉ Set.range (sU ≫ U.ι).base ∧ z ∉ Set.range (sU' ≫ U.ι).base)) ∧
      (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ W₂ → U.ι.base y ∈ W₃ →
        f.base y ∈ (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen a' ⊔ Mdl.basicOpen b')) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_opens_sup_eq_top_and_forall_mem_basicOpen_of_crossingChart_of_sections.solution
