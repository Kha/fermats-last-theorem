import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed
    {R : Type} [CommRing R] {K : Type} [Field K] [IsAlgClosed K] (A : ValuationSubring K) [HenselianLocalRing ↥A]
    (ι : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    (n : ℕ)
    [LocallyQuasiFinite ((L.baseChange ι).schemeKerStr n)] [QuasiCompact ((L.baseChange ι).schemeKerStr n)]
    [Flat ((L.baseChange ι).schemeKerStr n)]
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ ι) f)
    (hy : L.IsTorsionPoint (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ ι) n y) :
    ∃ s : SchemeHomOver ι f, L.IsTorsionPoint ι n s ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1 = y.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed.solution
