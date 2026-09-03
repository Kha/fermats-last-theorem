import Definitions.Def_WeierstrassCurve_VeluVariableChange
import Definitions.Def_WeierstrassCurve_VeluQuotientOfSums
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights

theorem WeierstrassCurve.variableChange_veluQuotientOfSums_asymWeights {K : Type*} [Field K] (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))
    (hneg : ∀ P ∈ S, (P.1, W.toAffine.negY P.1 P.2) ∈ S) :
    (C • W).veluQuotientOfSums
        (∑ P ∈ S.map (vcInvEmbedding C), (C • W).veluGx P.1 P.2)
        (∑ P ∈ S.map (vcInvEmbedding C),
          (P.1 * (C • W).veluGx P.1 P.2 - P.2 * (C • W).veluGy P.1 P.2)) =
      C • (W.veluQuotientOfSums (∑ P ∈ S, W.veluGx P.1 P.2)
        (∑ P ∈ S, (P.1 * W.veluGx P.1 P.2 - P.2 * W.veluGy P.1 P.2))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_variableChange_veluQuotientOfSums_asymWeights.solution
