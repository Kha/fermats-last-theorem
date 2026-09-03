import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (w w' : HeightOneSpectrum (𝓞 L)) (hw' : w'.asIdeal = σ • w.asIdeal) :
    ((AdelicDock.localEmbed (𝓞 L) L w).range.map (AdelicDock.finEmbed (𝓞 L) L)).map (sigmaAdelicAct K L D σ)
        = (AdelicDock.localEmbed (𝓞 L) L w').range.map (AdelicDock.finEmbed (𝓞 L) L) ∧
      (∃ u ∈ AdelicDock.localLevelOne (𝓞 L) L w' ⊤,
        sigmaAdelicAct K L D σ (heckeGen (𝓞 L) L w)
          = heckeGen (𝓞 L) L w' * AdelicDock.finEmbed (𝓞 L) L (AdelicDock.localEmbed (𝓞 L) L w' u)) ∧
      (((AdelicDock.localLevelOne (𝓞 L) L w ⊤).map (AdelicDock.localEmbed (𝓞 L) L w)).map
            (AdelicDock.finEmbed (𝓞 L) L)).map (sigmaAdelicAct K L D σ)
        = ((AdelicDock.localLevelOne (𝓞 L) L w' ⊤).map (AdelicDock.localEmbed (𝓞 L) L w')).map
            (AdelicDock.finEmbed (𝓞 L) L) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul.solution
