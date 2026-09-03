import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_apply_jOf_univ_eq_classify_act_eq

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.LevelModuliPackageAbs.exists_algEquiv_apply_jOf_univ_eq_classify_act_eq
    (A : Type) [CommRing A] (D : ModularCurve.LevelModuliDatum A) (P₀ : LevelModuliPackageAbs A D)
    (σ σ' : D.ProblemAut)
    (hσ : ∀ (T : Type) [CommRing T] [Algebra A T] (y : D.Pt T), σ'.act (σ.act y) = y)
    (hσ' : ∀ (T : Type) [CommRing T] [Algebra A T] (y : D.Pt T), σ.act (σ'.act y) = y) :
    ∃ e : P₀.B₀ ≃ₐ[A] P₀.B₀,
      e (D.jOf P₀.univ) = D.jOf P₀.univ ∧
      ∀ (T : Type) [CommRing T] [Algebra A T] (x : D.Pt T),
        P₀.classify (σ.act x) = (P₀.classify x).comp (e : P₀.B₀ →ₐ[A] P₀.B₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_apply_jOf_univ_eq_classify_act_eq.solution
