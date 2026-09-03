import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addEquiv_torsionBy_ratBaseChange_eq_padicMap_padicAlgClosure

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem WeierstrassCurve.exists_addEquiv_torsionBy_ratBaseChange_eq_padicMap_padicAlgClosure
    (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] (n : ℕ) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ c : Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ_[p])).Point n ≃+
          Submodule.torsionBy ℤ ((E.map (algebraMap ℚ ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point n,
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P,
        c (σ • P) = σ • c P := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addEquiv_torsionBy_ratBaseChange_eq_padicMap_padicAlgClosure.solution
