import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import P2M.Util
import P2M.Sol.S_Rep_nonempty_tateCohomology_trivial_iso_of_h1_h2
attribute [-simp] Rep.coe_tateδneg2_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.nonempty_tateCohomology_trivial_iso_of_h1_h2 {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (S : Subgroup G) [Fintype S] (q : ℤ) :
    Nonempty ((Rep.res S.subtype (Rep.trivial ℤ G ℤ)).tateCohomology q ≅ (Rep.res S.subtype C).tateCohomology (q + 2)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_nonempty_tateCohomology_trivial_iso_of_h1_h2.solution
