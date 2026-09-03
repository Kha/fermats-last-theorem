import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_Deformation_DieudonneModule_map_injective_and_exists_map_eq_of_isLocalRing_cartierDual
import P2M.Util
namespace P2MW.S_Deformation_DieudonneModule_exists_bijective_map_eq_of_addEquiv_of_isLocalRing_cartierDual
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul

set_option autoImplicit false

universe u v

open Function

namespace HondaIsoPsi

variable (p : ℕ) [Fact p.Prime]

private theorem symm_comm {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (FX : X →+ X) (FY : Y →+ Y) (h : ∀ z, e (FX z) = FY (e z)) (w : Y) :
    e.symm (FY w) = FX (e.symm w) := by
  apply e.injective
  rw [e.apply_symm_apply, h, e.apply_symm_apply]

end HondaIsoPsi

open HondaIsoPsi in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A]
    (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B]
    (hA : IsLocalRing (CartierDual (ZMod p) A)) (hB : IsLocalRing (CartierDual (ZMod p) B))
    (e : Deformation.DieudonneModule (ZMod p) p B ≃+ Deformation.DieudonneModule (ZMod p) p A)
    (heF : ∀ z, e (Deformation.DieudonneModule.frobenius (ZMod p) p B z) =
      Deformation.DieudonneModule.frobenius (ZMod p) p A (e z))
    (heV : ∀ z, e (Deformation.DieudonneModule.verschiebung (ZMod p) p B z) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p A (e z)) :
    ∃ g : B →ₐc[ZMod p] A, Function.Bijective g ∧
      Deformation.DieudonneModule.map (ZMod p) p g = e.toAddMonoidHom := by
  obtain ⟨-, hfullBA⟩ :=
    Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual p A B hA hB
  obtain ⟨-, hfullAB⟩ :=
    Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual p B A hB hA
  obtain ⟨hfaithAA, -⟩ :=
    Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual p A A hA hA
  obtain ⟨hfaithBB, -⟩ :=
    Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual p B B hB hB
  obtain ⟨g, hg⟩ := hfullBA e.toAddMonoidHom heF heV
  have heF' := HondaIsoPsi.symm_comm e (Deformation.DieudonneModule.frobenius (ZMod p) p B)
    (Deformation.DieudonneModule.frobenius (ZMod p) p A) heF
  have heV' := HondaIsoPsi.symm_comm e (Deformation.DieudonneModule.verschiebung (ZMod p) p B)
    (Deformation.DieudonneModule.verschiebung (ZMod p) p A) heV
  obtain ⟨g', hg'⟩ := hfullAB e.symm.toAddMonoidHom heF' heV'

  have h1 : g.comp g' = BialgHom.id (ZMod p) A := by
    apply hfaithAA
    ext z
    rw [Deformation.DieudonneModule.map_comp, Deformation.DieudonneModule.map_id, hg, hg']
    exact e.apply_symm_apply z
  have h2 : g'.comp g = BialgHom.id (ZMod p) B := by
    apply hfaithBB
    ext z
    rw [Deformation.DieudonneModule.map_comp, Deformation.DieudonneModule.map_id, hg, hg']
    exact e.symm_apply_apply z
  refine ⟨g, ⟨?_, ?_⟩, hg⟩
  ·
    intro x y hxy
    have := congrArg g' hxy
    have hx : g' (g x) = x := DFunLike.congr_fun h2 x
    have hy : g' (g y) = y := DFunLike.congr_fun h2 y
    rw [hx, hy] at this
    exact this
  ·
    intro a
    exact ⟨g' a, DFunLike.congr_fun h1 a⟩
