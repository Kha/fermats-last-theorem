import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_isZero_tateCohomology_of_isPGroup_of_forall
attribute [-simp] Rep.coe_tateδneg2_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.isZero_tateCohomology_of_isPGroup_of_forall {k P : Type u} [CommRing k] [Group P] [Fintype P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (B : Rep.{u} k P)
    (h : ∀ (Q : Type u) [Group Q] [Fintype Q] (g : Q →* P), Function.Injective g →
      ∃ q : ℤ, CategoryTheory.Limits.IsZero ((Rep.res g B).tateCohomology q) ∧
        CategoryTheory.Limits.IsZero ((Rep.res g B).tateCohomology (q + 1)))
    (n : ℤ) : CategoryTheory.Limits.IsZero (B.tateCohomology n) := by p2m_exact_reverting @_root_.P2MW.S_Rep_isZero_tateCohomology_of_isPGroup_of_forall.solution
