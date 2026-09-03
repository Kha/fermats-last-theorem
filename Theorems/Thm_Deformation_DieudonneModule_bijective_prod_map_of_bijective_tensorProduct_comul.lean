import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_bijective_prod_map_of_bijective_tensorProduct_comul

open scoped TensorProduct
open MvPowerSeries

universe v

theorem Deformation.DieudonneModule.bijective_prod_map_of_bijective_tensorProduct_comul
    (p : ℕ) [Fact p.Prime]
    (B : Type v) [CommRing B] [Bialgebra (ZMod p) B]
    (Gc Ge : Type v) [CommRing Gc] [Bialgebra (ZMod p) Gc] [CommRing Ge] [Bialgebra (ZMod p) Ge]
    (qc : B →ₐc[ZMod p] Gc) (πe : B →ₐc[ZMod p] Ge) (Θ : B →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hΘ : Function.Bijective Θ)
    (hΘapply : ∀ b, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Gc) (πe : B →ₐ[ZMod p] Ge)
      (Coalgebra.comul (R := ZMod p) b)) :
    Function.Bijective fun z : Deformation.DieudonneModule (ZMod p) p B =>
      (Deformation.DieudonneModule.map (ZMod p) p qc z, Deformation.DieudonneModule.map (ZMod p) p πe z) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_bijective_prod_map_of_bijective_tensorProduct_comul.solution
