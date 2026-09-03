import Definitions.Def_HeckeGalois_EichlerShimura
import P2M.Util
import P2M.Sol.S_ModularCurve_FrobeniusQuadratic_of_specializationExists

theorem ModularCurve.FrobeniusQuadratic.of_specializationExists {K L : Type*} [Field K] [Field L] [Algebra K L] (N p : ℕ) (J : Type*) [AddCommGroup J] [Module ModularCurve.HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) ModularCurve.HeckeAlg J] (h : ModularCurve.SpecializationExists (K := K) (L := L) N p J) : ModularCurve.FrobeniusQuadratic (K := K) (L := L) N p J := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FrobeniusQuadratic_of_specializationExists.solution
