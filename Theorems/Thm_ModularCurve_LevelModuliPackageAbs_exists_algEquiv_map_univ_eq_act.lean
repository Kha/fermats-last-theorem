import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq_act

set_option autoImplicit false

universe u

theorem ModularCurve.LevelModuliPackageAbs.exists_algEquiv_map_univ_eq_act
    {A : Type u} [CommRing A] {D : ModularCurve.LevelModuliDatum.{u} A} (P : ModularCurve.LevelModuliPackageAbs A D)
    (ρ ρ' : D.ProblemAut)
    (h₁ : ∀ (T : Type u) [CommRing T] [Algebra A T] (y : D.Pt T), ρ'.act (ρ.act y) = y)
    (h₂ : ∀ (T : Type u) [CommRing T] [Algebra A T] (y : D.Pt T), ρ.act (ρ'.act y) = y) :
    ∃ σ : P.B₀ ≃ₐ[A] P.B₀,
      D.map (σ : P.B₀ →ₐ[A] P.B₀) P.univ = ρ.act P.univ ∧
      D.map (σ.symm : P.B₀ →ₐ[A] P.B₀) P.univ = ρ'.act P.univ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq_act.solution
