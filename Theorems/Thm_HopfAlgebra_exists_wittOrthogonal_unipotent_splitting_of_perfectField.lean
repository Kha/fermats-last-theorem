import Mathlib
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField
attribute [-instance] CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

universe u v w

theorem HopfAlgebra.exists_wittOrthogonal_unipotent_splitting_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A] :
    ∃ (Aw : Type v) (_ : CommRing Aw) (_ : HopfAlgebra k Aw) (_ : Module.Finite k Aw)
      (_ : Coalgebra.IsCocomm k Aw)
      (Au : Type v) (_ : CommRing Au) (_ : HopfAlgebra k Au) (_ : Module.Finite k Au)
      (_ : Coalgebra.IsCocomm k Au)
      (μ : A →ₐc[k] Aw) (ι : Au →ₐc[k] A),
      Function.Surjective μ ∧ Function.Injective ι ∧
      (∀ a : A, a ∈ HopfAlgebra.hopfKer μ ↔ a ∈ Set.range ι) ∧
      IsLocalRing (CartierDual k Au) ∧
      (∀ (D : Type w) [CommRing D] [Bialgebra k D] (φ : A →ₐc[k] D), Function.Surjective φ →
        (∀ a : A, μ a = 0 → φ a = 0) →
          ∀ (m : ℕ) (y : Deformation.wittHom k p m D), y = 0) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_wittOrthogonal_unipotent_splitting_of_perfectField.solution
