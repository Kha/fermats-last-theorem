import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_existsUnique_bialgHom_comp_eq_comp_of_surjective_of_isLocalRing_of_isReduced_of_ker_eq_map_zmodp

set_option autoImplicit false

theorem HopfAlgebra.existsUnique_bialgHom_comp_eq_comp_of_surjective_of_isLocalRing_of_isReduced_of_ker_eq_map_zmodp
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    (Gc : Type) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc] [Module.Finite (ZMod p) Gc]
    (Ge : Type) [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge] [Module.Finite (ZMod p) Ge]

    (qc : B →ₐc[ZMod p] Gc) (σ : Ge →ₐc[ZMod p] B)
    (hGc : IsLocalRing Gc) (hGe : IsReduced Ge) (hqc : Function.Surjective qc)
    (hkerqc : RingHom.ker (qc : B →ₐ[ZMod p] Gc) =
      Ideal.map (σ : Ge →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Ge)))
    (g : B →ₐc[ZMod p] B) :
    ∃! gc : Gc →ₐc[ZMod p] Gc, gc.comp qc = qc.comp g := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_existsUnique_bialgHom_comp_eq_comp_of_surjective_of_isLocalRing_of_isReduced_of_ker_eq_map_zmodp.solution
