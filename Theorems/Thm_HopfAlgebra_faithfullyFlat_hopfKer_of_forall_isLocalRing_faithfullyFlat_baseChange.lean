import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange

theorem HopfAlgebra.faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H')
    (hloc : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧
        Module.FaithfullyFlat
          ↥(HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
              TensorProduct R R₁ H →ₐc[R₁] TensorProduct R R₁ H'))
          (TensorProduct R R₁ H)) :
    Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange.solution
