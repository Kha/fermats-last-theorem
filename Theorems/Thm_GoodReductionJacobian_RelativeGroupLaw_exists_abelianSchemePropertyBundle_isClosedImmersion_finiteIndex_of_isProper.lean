import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {N : Scheme.{u}}
    {gN : N ⟶ Spec (CommRingCat.of k)} [IsProper gN] (LN : RelativeGroupLaw k gN) :
    ∃ (A : Scheme.{u}) (fA : A ⟶ Spec (CommRingCat.of k)) (LA : RelativeGroupLaw k fA) (d : ℕ)
      (ι : SchemeHomOver fA gN),
      LA.IsCommutative ∧ AbelianSchemePropertyBundle k fA ∧ SmoothOfRelativeDimension d fA ∧
      IsClosedImmersion ι.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t fA),
        NeronModelInfra.schemeHomOverComp (LA.mul t x y) ι =
          LN.mul t (NeronModelInfra.schemeHomOverComp x ι)
            (NeronModelInfra.schemeHomOverComp y ι)) ∧
      ∃ S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN), S.Finite ∧
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN,
          ∃ s ∈ S, ∃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) fA,
            x = LN.mul (𝟙 (Spec (CommRingCat.of k))) s
              (NeronModelInfra.schemeHomOverComp a ι) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isClosedImmersion_finiteIndex_of_isProper.solution
