import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_LevelData_restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle
attribute [-simp] HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.JZeroNeronObjectAtP

open ModularCurve in

theorem ModularCurve.JHNeronObjectAtP.LevelData.restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ base p)

    {h : ℕ} (𝒜 : PDivisibleGroup (baseRing p) p h)
    [Algebra (baseRing p) (ZMod p)]
    (hσp : σp = Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) (ZMod p))))
    (ι' : ∀ v : ℕ, Spec (CommRingCat.of ((𝒜.baseChange (ZMod p)).level v)) ⟶ pullback Λ.f σp)
    (hι'base : ∀ v : ℕ, ι' v ≫ pullback.snd Λ.f σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((𝒜.baseChange (ZMod p)).level v))))
    (hι'cl : ∀ v : ℕ, IsClosedImmersion (ι' v))
    (hι'p : ∀ (v : ℕ), ∃ h3 : ι' v ≫ (Λ.L.baseChange σp).schemeNsmul (p ^ v) =
          (ι' v ≫ pullback.snd Λ.f σp) ≫ ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1,
      IsIso (pullback.lift (f := (Λ.L.baseChange σp).schemeNsmul (p ^ v)) (g := ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1)
        (ι' v) (ι' v ≫ pullback.snd Λ.f σp) h3))

    (hι'mul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒜.baseChange (ZMod p)).Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v =
          ((Λ.L.baseChange σp).mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

    (hι't : ∀ v : ℕ, Spec.map (CommRingCat.ofHom
          ((𝒜.baseChange (ZMod p)).transition v : (𝒜.baseChange (ZMod p)).level (v + 1) →+* (𝒜.baseChange (ZMod p)).level v)) ≫ ι' (v + 1) = ι' v)

    (F V : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p]
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) (RelativeGroupLaw.baseChangeStr σp Λ.f)),
      (schemeHomOverComp x F).1 = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x.1)
    (hVF : V.1 ≫ F.1 = (Λ.L.baseChange σp).schemeNsmul p)
    (hFV : F.1 ≫ V.1 = (Λ.L.baseChange σp).schemeNsmul p)
    (hVmul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp Λ.f)),
        schemeHomOverComp ((Λ.L.baseChange σp).mul s x y) V =
          (Λ.L.baseChange σp).mul s (schemeHomOverComp x V) (schemeHomOverComp y V))

    (φF φV : ∀ v : ℕ, (𝒜.baseChange (ZMod p)).level v →ₐc[ZMod p] (𝒜.baseChange (ZMod p)).level v)
    (hφF : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φF v : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v)) ≫ ι' v = ι' v ≫ F.1)
    (hφV : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φV v : (𝒜.baseChange (ZMod p)).level v →+* (𝒜.baseChange (ZMod p)).level v)) ≫ ι' v = ι' v ≫ V.1) :
    (∀ (v : ℕ) (a : (𝒜.baseChange (ZMod p)).level v), φF v a = a ^ p) ∧
    (∀ (v : ℕ) (χ : CartierDual (ZMod p) ((𝒜.baseChange (ZMod p)).level v)), CartierDual.map (φV v) χ = χ ^ p) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_restrict_frobenius_eq_pow_and_cartierDual_map_restrict_verschiebung_eq_pow_of_abelianSchemePropertyBundle.solution
