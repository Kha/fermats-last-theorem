import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_Dimension
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_finrank_cotangent_one_add_finrank_cotangent_one_eq_height
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.finrank_cotangent_one_add_finrank_cotangent_one_eq_height
    {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {h : ℕ}
    {G G' : PDivisibleGroup k p h} (D : G.CartierDuality G') :
    Module.finrank k (G.Cotangent 1) + Module.finrank k (G'.Cotangent 1) = h := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_finrank_cotangent_one_add_finrank_cotangent_one_eq_height.solution
