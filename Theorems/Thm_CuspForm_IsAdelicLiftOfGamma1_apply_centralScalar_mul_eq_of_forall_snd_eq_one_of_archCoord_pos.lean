import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_RatIdele_Normalizer
import P2M.Util
import P2M.Sol.S_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos

set_option autoImplicit false

open NumberField AutomorphicForm

theorem CuspForm.IsAdelicLiftOfGamma1.apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos
    {M : ℕ} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) (hM : M ≠ 0)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hz : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), (z : AdeleRing (𝓞 ℚ) ℚ).2 v = 1)
    (hpos : 0 < RatIdele.archCoord z)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (centralScalar (𝓞 ℚ) ℚ z * x) = Φ x := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos.solution
