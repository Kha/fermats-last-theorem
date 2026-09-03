import Definitions.Def_ModularCurve_JHNodeDepth
import P2M.Util
import P2M.Sol.S_ModularCurve_JHPlaceSpecialization_exists_depth_forall_annulusDepthLaw
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.JHPlaceSpecialization.exists_depth_forall_annulusDepthLaw
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (P : JHPlaceSpecialization p M H hpM A)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s ∈ SS, ∀ s' ∈ SS, s.1 = s'.1 → s = s')
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hz : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • (An s).param = (An s).param)
    (hdom : ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      P.reduceFst α hα V = s.1.1 →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) →
      V ∈ (An s).dom) :
    ∃ depth : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℕ,
      (∀ s : ↥SS, P.AnnulusDepthLaw α hα (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (An s) depth) ∧
      (∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
        P.reduceFst α hα V = s.1.1 →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) →
        1 ≤ depth V ∧
          A.valuation (((An s).modulus : ↥A) : AlgebraicClosure ℚ) < A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ depth V) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (∀ s : ↥SS, P.reduceFst α hα V ≠ s.1.1) → depth V = 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHPlaceSpecialization_exists_depth_forall_annulusDepthLaw.solution
