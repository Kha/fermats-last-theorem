import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_Diamond_exists_represents_raw_trivial_rigidDataH1Pow

set_option autoImplicit false

universe u

open ModularCurve
theorem ModularCurve.FullLevel.Diamond.exists_represents_raw_trivial_rigidDataH1Pow
    (A : Type u) [CommRing A] (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hℓ5 : 5 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hNA : IsUnit ((N : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r))) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.FiniteType A C)
      (xᵤ : ((((ModularCurve.gamma0PowComponent A N hN).prod
            ((ModularCurve.gamma1Component A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).restrict
            (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
            (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
            (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Raw C),
      ∀ (T : Type u) [CommRing T] [Algebra A T]
        (x : ((((ModularCurve.gamma0PowComponent A N hN).prod
            ((ModularCurve.gamma1Component A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).restrict
            (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
            (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
            (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Raw T),
        ∃! ψ : C →ₐ[A] T,
          ((((ModularCurve.gamma0PowComponent A N hN).prod
            ((ModularCurve.gamma1Component A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).restrict
            (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
            (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
            (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).mapRing ψ xᵤ = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_Diamond_exists_represents_raw_trivial_rigidDataH1Pow.solution
