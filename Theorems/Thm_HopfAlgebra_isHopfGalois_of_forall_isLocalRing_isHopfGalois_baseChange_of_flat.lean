import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat

theorem HopfAlgebra.isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (hloc : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧
        HopfAlgebra.IsHopfGalois (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
            TensorProduct R R₁ H →ₐc[R₁] TensorProduct R R₁ H')) :
    HopfAlgebra.IsHopfGalois qc := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat.solution
