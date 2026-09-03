import Definitions.Def_NarrowRayClassGroup
import P2M.Util
import P2M.Sol.S_M4aKummer_normClassIndex_dvd_mul_of_tower

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply

theorem M4aKummer.normClassIndex_dvd_mul_of_tower
    (k M E : Type*) [Field k] [NumberField k] [Field M] [NumberField M] [Field E] [NumberField E]
    [Algebra k M] [Algebra M E] [Algebra k E] [IsScalarTower k M E] (𝔣 : Ideal (𝓞 k)) :
    ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
      ((coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map
        (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
          primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
        (coprimeToModulus k 𝔣)).index
    ∣ ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
        ((coprimeToModulus M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))).map
          (raySymbolUnitsHom M (fun u : HeightOneSpectrum (𝓞 M) =>
            primeUnit k (u.under (𝓞 k)) ^ ((u.under (𝓞 k)).asIdeal.inertiaDeg' u.asIdeal)))).subgroupOf
          (coprimeToModulus k 𝔣)).index
      * ((narrowRaySubgroup M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))).subgroupOf
            (coprimeToModulus M (𝔣.map (algebraMap (𝓞 k) (𝓞 M)))) ⊔
          ((coprimeToModulus E ((𝔣.map (algebraMap (𝓞 k) (𝓞 M))).map (algebraMap (𝓞 M) (𝓞 E)))).map
            (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
              primeUnit M (w.under (𝓞 M)) ^ ((w.under (𝓞 M)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
            (coprimeToModulus M (𝔣.map (algebraMap (𝓞 k) (𝓞 M))))).index := by p2m_exact_reverting @_root_.P2MW.S_M4aKummer_normClassIndex_dvd_mul_of_tower.solution
