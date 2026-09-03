import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_exists_dualTwist_linearEquiv_dual

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem ResidualGaloisRep.exists_dualTwist_linearEquiv_dual
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p] (ρbar : ResidualGaloisRep k) :
    ∃ (ρbar' : ResidualGaloisRep k) (η : ρbar'.V ≃ₗ[k] Module.Dual k ρbar.V),
      ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ρbar'.V),
        η (ρbar'.ρ g w) =
          (ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)) • ((η w) ∘ₗ (ρbar.ρ g⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_exists_dualTwist_linearEquiv_dual.solution
