import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isStrictOrdinaryAt_of_isStrictOrdinaryAt_baseChangeAlong_of_injective
attribute [-instance] TateModule.instModule TateModule.instSMul
attribute [-simp] TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply

set_option autoImplicit false

theorem GaloisRepAdic.isStrictOrdinaryAt_of_isStrictOrdinaryAt_baseChangeAlong_of_injective
    {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharZero A]
    [CommRing B] [IsLocalRing B] [IsDomain B] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (hinj : Function.Injective φ)
    (ρ : GaloisRepAdic A) (p : ℕ) (hp : p.Prime)
    (h : (ρ.baseChangeAlong φ hφ).IsStrictOrdinaryAt p) :
    ρ.IsStrictOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_isStrictOrdinaryAt_baseChangeAlong_of_injective.solution
