import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelModuliPackageAbs_exists_eq_act_mapRing_of_ker_classify_eq

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.LevelModuliPackageAbs.exists_eq_act_mapRing_of_ker_classify_eq
    (A : Type) [CommRing A] (Rd : ModularCurve.RigidWeierstrassData A)
    (P₀ : LevelModuliPackageAbs A Rd.toLevelModuliDatum)
    (K : Type) [CommRing K] [Algebra A K]
    (x₁ x₂ : Rd.toLevelModuliDatum.Pt K)
    (h : RingHom.ker (P₀.classify x₁).toRingHom = RingHom.ker (P₀.classify x₂).toRingHom)
    (y₁ y₂ : Rd.Raw K)
    (hy₁ : (Quot.mk _ y₁ : Rd.Pt K) = x₁) (hy₂ : (Quot.mk _ y₂ : Rd.Pt K) = x₂) :
    ∃ (w : Rd.Raw ↥(P₀.classify x₁).range) (κ₁ κ₂ : ↥(P₀.classify x₁).range →ₐ[A] K)
      (C₁ C₂ : WeierstrassCurve.VariableChange K),
      Function.Injective κ₁ ∧ Function.Injective κ₂ ∧ (∀ r : ↥(P₀.classify x₁).range, κ₁ r = (r : K)) ∧
      y₁ = Rd.act C₁ (Rd.mapRing κ₁ w) ∧ y₂ = Rd.act C₂ (Rd.mapRing κ₂ w) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_eq_act_mapRing_of_ker_classify_eq.solution
