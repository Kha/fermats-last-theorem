import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_ModularCurve_JHNeronObjectAtP_exists_iso_torus_kerPair_abqFibre

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP AlgebraicCurve
open scoped TensorProduct

theorem ModularCurve.JHNeronObjectAtP.exists_iso_torus_kerPair_abqFibre
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (hΛ : IsProper Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    ∃ e : torusScheme (ResidueField ↥A) O.toricRank ≅
        RelativeGroupLaw.kerPair (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre,
      e.hom ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre = O.torusFibre.1 ∧
      ∀ n : ℕ, e.hom ≫ (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA))
          (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeNsmul n =
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫
          e.hom := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHNeronObjectAtP_exists_iso_torus_kerPair_abqFibre.solution
