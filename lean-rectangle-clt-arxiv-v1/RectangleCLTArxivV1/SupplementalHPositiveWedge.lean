import RectangleCLTArxivV1.SupplementalHSphericalSectors
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The actual positive planar wedge has angular area equal to the angle
between its unit endpoint rays. No principal-sector equality is assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set Metric
open scoped InnerProductSpace ComplexConjugate
noncomputable section

def positivePlanarWedge {E : Type*} [AddCommGroup E] [Module ℝ E] (u v : E) : Set E :=
  {z | ∃ a b : ℝ, 0≤a ∧ 0≤b ∧ z=a • u+b • v}

theorem positivePlanarWedge_dilation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (u v : E) (r : ℝ) (hr : 0<r) (z : E) :
    r • z∈positivePlanarWedge u v ↔ z∈positivePlanarWedge u v := by
  constructor
  · rintro ⟨a,b,ha,hb,he⟩
    refine ⟨a/r,b/r,div_nonneg ha hr.le,div_nonneg hb hr.le,?_⟩
    have hh := congrArg (fun w : E => r⁻¹ • w) he
    simpa only [smul_add,smul_smul,inv_mul_cancel₀ hr.ne',one_smul,div_eq_mul_inv,mul_comm] using hh
  · rintro ⟨a,b,ha,hb,rfl⟩
    exact ⟨r*a,r*b,mul_nonneg hr.le ha,mul_nonneg hr.le hb,by rw [smul_add,smul_smul,smul_smul]⟩

/-- Explicit planar coefficients identify the positive wedge with two
actual closed halfplanes, when the second ray has positive imaginary part. -/
theorem positivePlanarWedge_one_iff {v z : ℂ} (hv : 0<v.im) :
    z∈positivePlanarWedge 1 v ↔ 0≤z.im ∧ 0≤v.im*z.re-v.re*z.im := by
  constructor
  · rintro ⟨a,b,ha,hb,rfl⟩
    simp only [Complex.add_im,Complex.add_re,Complex.smul_im,Complex.smul_re,
      Complex.one_im,Complex.one_re,smul_eq_mul,mul_zero,zero_add,mul_one]
    constructor
    · exact mul_nonneg hb hv.le
    · nlinarith
  · rintro ⟨hi,hd⟩
    refine ⟨(v.im*z.re-v.re*z.im)/v.im,z.im/v.im,
      div_nonneg hd hv.le,div_nonneg hi hv.le,?_⟩
    apply Complex.ext
    · simp only [Complex.add_re,Complex.smul_re,Complex.one_re,smul_eq_mul,mul_one]
      field_simp
      ring
    · simp only [Complex.add_im,Complex.smul_im,Complex.one_im,smul_eq_mul,mul_zero,zero_add]
      exact (div_mul_cancel₀ z.im hv.ne').symm

theorem positivePlanarWedge_one_measurable {v : ℂ} (hv : 0<v.im) :
    MeasurableSet (positivePlanarWedge 1 v) := by
  have he : positivePlanarWedge 1 v={z : ℂ | 0≤z.im ∧ 0≤v.im*z.re-v.re*z.im} :=
    Set.ext (fun _ => positivePlanarWedge_one_iff hv)
  rw [he]
  exact (measurableSet_le measurable_const Complex.measurable_im).inter
    (measurableSet_le measurable_const
      (show Measurable (fun z : ℂ => v.im*z.re-v.re*z.im) from by fun_prop))

private theorem sin_nonneg_iff_on_principal {x : ℝ} (hx : -Real.pi<x) (hxp : x<Real.pi) :
    0≤Real.sin x ↔ 0≤x := by
  constructor
  · intro h
    by_contra hn
    exact (Real.sin_neg_of_neg_of_neg_pi_lt (lt_of_not_ge hn) hx).not_le h
  · intro h
    exact Real.sin_nonneg_of_mem_Icc ⟨h,hxp.le⟩

theorem positivePlanarWedge_canonical_polar_iff (θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi)
    (r φ : ℝ) (hr : 0<r) (hφ : φ∈Ioo (-Real.pi) Real.pi) :
    Complex.polarCoord.symm (r,φ)∈positivePlanarWedge 1
      ((Real.cos θ : ℂ)+Real.sin θ*Complex.I) ↔ φ∈Icc 0 θ := by
  have hsθ : 0<Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  rw [positivePlanarWedge_one_iff (by simpa using hsθ)]
  simp only [Complex.polarCoord_symm_apply,Complex.mul_im,Complex.mul_re,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,sub_zero,zero_add,add_zero]
  have hd : Real.sin θ*(r*Real.cos φ)-Real.cos θ*(r*Real.sin φ)=r*Real.sin (θ-φ) := by
    rw [Real.sin_sub]
    ring
  rw [hd]
  constructor
  · rintro ⟨h1,h2⟩
    have hφ0 : 0≤φ := (sin_nonneg_iff_on_principal hφ.1 hφ.2).mp
      ((mul_nonneg_iff_of_pos_left hr).mp h1)
    have hs : 0≤Real.sin (θ-φ) := (mul_nonneg_iff_of_pos_left hr).mp h2
    have hδ : 0≤θ-φ :=
      (sin_nonneg_iff_on_principal (by linarith [hφ.2]) (by linarith)).mp hs
    exact ⟨hφ0,by linarith⟩
  · intro h
    exact ⟨mul_nonneg hr.le (Real.sin_nonneg_of_mem_Icc ⟨h.1,h.2.trans hθπ.le⟩),
      mul_nonneg hr.le (Real.sin_nonneg_of_mem_Icc ⟨by linarith [h.2],by linarith [h.1]⟩)⟩

/-- Direct polar integration over the actual generated positive wedge.
The boundary rays are included, so no asserted arc/set equivalence or
boundary-null reduction is needed. -/
theorem positivePlanarWedge_canonical_gaussian_mass (θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) :
    (∫ z in positivePlanarWedge (1 : ℂ) ((Real.cos θ : ℂ)+Real.sin θ*Complex.I),
      Real.exp (-‖z‖^2/2))=θ := by
  let v : ℂ := (Real.cos θ : ℂ)+Real.sin θ*Complex.I
  have hv : 0<v.im := by simpa [v] using Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  rw [← integral_indicator (positivePlanarWedge_one_measurable hv),
    ← Complex.integral_comp_polarCoord_symm]
  have he (p : ℝ × ℝ) (hp : p∈polarCoord.target) :
      p.1 • (positivePlanarWedge 1 v).indicator (fun z : ℂ => Real.exp (-‖z‖^2/2))
        (Complex.polarCoord.symm p)=
      (p.1*Real.exp (-p.1^2/2))*(Icc 0 θ).indicator (fun _ => (1 : ℝ)) p.2 := by
    have hiff := positivePlanarWedge_canonical_polar_iff θ hθ hθπ p.1 p.2 hp.1 hp.2
    change Complex.polarCoord.symm p∈positivePlanarWedge 1 v ↔ p.2∈Icc 0 θ at hiff
    by_cases h : p.2∈Icc 0 θ
    · rw [Set.indicator_of_mem (hiff.mpr h),Set.indicator_of_mem h,
        Complex.norm_polarCoord_symm,abs_of_pos hp.1,smul_eq_mul,mul_one]
    · rw [Set.indicator_of_not_mem (fun hz => h (hiff.mp hz)),Set.indicator_of_not_mem h,
        smul_zero,mul_zero]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet he]
  change (∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
      (p.1*Real.exp (-p.1^2/2))*(Icc 0 θ).indicator (fun _ => (1 : ℝ)) p.2)=_
  rw [Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r : ℝ => r*Real.exp (-r^2/2))
      ((Icc 0 θ).indicator (fun _ => (1 : ℝ))) (Ioi 0) (Ioo (-Real.pi) Real.pi),
    supplementalH_integral_radial_two,one_mul,setIntegral_indicator measurableSet_Icc]
  have hs : Icc 0 θ⊆Ioo (-Real.pi) Real.pi := by
    intro x hx
    exact ⟨by linarith [Real.pi_pos,hx.1],hx.2.trans_lt hθπ⟩
  rw [Set.inter_eq_right.mpr hs]
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one,
    Real.volume_real_Icc_of_le hθ.le,sub_zero]

theorem positivePlanarWedge_canonical_angular_area (θ : ℝ) (hθ : 0<θ) (hθπ : θ<Real.pi) :
    (volume : Measure ℂ).toSphere.real (supplementalHSphericalSection
      (positivePlanarWedge (1 : ℂ) ((Real.cos θ : ℂ)+Real.sin θ*Complex.I)))=θ := by
  rw [← supplementalH_planar_cone_gaussian_mass volume Complex.finrank_real_complex _
    (positivePlanarWedge_one_measurable (by simpa using Real.sin_pos_of_pos_of_lt_pi hθ hθπ))
    (fun r hr z => positivePlanarWedge_dilation _ _ r hr z)]
  exact positivePlanarWedge_canonical_gaussian_mass θ hθ hθπ

theorem positivePlanarWedge_isometry_image {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (L : E ≃ₗᵢ[ℝ] F) (u v : E) :
    L '' positivePlanarWedge u v=positivePlanarWedge (L u) (L v) := by
  ext z
  constructor
  · rintro ⟨w,⟨a,b,ha,hb,rfl⟩,rfl⟩
    exact ⟨a,b,ha,hb,by rw [map_add,map_smul,map_smul]⟩
  · rintro ⟨a,b,ha,hb,rfl⟩
    exact ⟨a • u+b • v,⟨a,b,ha,hb,rfl⟩,by rw [map_add,map_smul,map_smul]⟩

theorem positivePlanarWedge_gaussian_mass_isometry {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E ≃ₗᵢ[ℝ] F) (u v : E) :
    (∫ z in positivePlanarWedge (L u) (L v), Real.exp (-‖z‖^2/2))=
      ∫ z in positivePlanarWedge u v, Real.exp (-‖z‖^2/2) := by
  rw [← positivePlanarWedge_isometry_image L u v,
    L.measurePreserving.setIntegral_image_emb L.toMeasurableEquiv.measurableEmbedding]
  simp only [L.norm_map]

theorem exists_positive_wedge_complex_isometry (u v : ℂ) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hp : u+v≠0) (hm : u-v≠0) :
    ∃ L : ℂ ≃ₗᵢ[ℝ] ℂ, L u=1 ∧ 0<(L v).im := by
  let q : Circle := ⟨conj u,by
    apply mem_sphere_zero_iff_norm.mpr
    simpa using hu⟩
  let R := rotation q
  have hRu : R u=1 := by
    change conj u*u=1
    rw [Complex.conj_mul',hu]
    norm_num
  have hw : ‖R v‖=1 := (R.norm_map v).trans hv
  have hIm : (R v).im≠0 := by
    intro hz
    have hs : (R v).re^2=1 := by
      have hh : (R v).re^2+(R v).im^2=1 := by
        calc
          _ = Complex.normSq (R v) := by simp only [Complex.normSq_apply,pow_two]
          _ = ‖R v‖^2 := Complex.normSq_eq_norm_sq _
          _ = 1 := by rw [hw,one_pow]
      simpa only [hz,zero_pow (by decide : (2 : ℕ)≠0),add_zero] using hh
    rcases sq_eq_one_iff.mp hs with hre | hre
    · have hRv : R v=1 := Complex.ext hre (by simpa using hz)
      have heq : v=u := R.injective (hRv.trans hRu.symm)
      exact hm (by rw [heq,sub_self])
    · have hRv : R v= -1 := Complex.ext hre (by simpa using hz)
      apply hp
      apply R.injective
      rw [map_add,hRu,hRv,map_zero]
      simp
  rcases lt_or_gt_of_ne hIm with hn | hpos
  · refine ⟨R.trans Complex.conjLIE,?_,?_⟩
    · change conj (R u)=1
      rw [hRu,map_one]
    · change 0< -(R v).im
      linarith
  · exact ⟨R,hRu,hpos⟩

theorem positivePlanarWedge_complex_measurable (u v : ℂ) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hp : u+v≠0) (hm : u-v≠0) : MeasurableSet (positivePlanarWedge u v) := by
  obtain ⟨L,hLu,hLv⟩ := exists_positive_wedge_complex_isometry u v hu hv hp hm
  have hc : MeasurableSet (positivePlanarWedge (L u) (L v)) := by
    rw [hLu]
    exact positivePlanarWedge_one_measurable hLv
  have hh := hc.preimage L.continuous.measurable
  rw [← positivePlanarWedge_isometry_image L u v,Set.preimage_image_eq _ L.injective] at hh
  exact hh

/-- The Gaussian area of the positive wedge between arbitrary nonparallel
unit rays is their ordinary unoriented angle. Rotation and reflection
reduce to the explicitly integrated actual canonical positive cone. -/
theorem positivePlanarWedge_complex_gaussian_mass (u v : ℂ) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hp : u+v≠0) (hm : u-v≠0) :
    (∫ z in positivePlanarWedge u v, Real.exp (-‖z‖^2/2))=Real.arccos ⟪u,v⟫_ℝ := by
  obtain ⟨L,hLu,hLv⟩ := exists_positive_wedge_complex_isometry u v hu hv hp hm
  let w := L v
  have hw : ‖w‖=1 := (L.norm_map v).trans hv
  have hIm : 0<w.im := hLv
  have hθ0 : 0<Complex.arg w := by
    have hnonneg : 0≤Complex.arg w := Complex.arg_nonneg_iff.mpr hIm.le
    have hne : Complex.arg w≠0 := by
      intro hz
      have hs : Real.sin (Complex.arg w)=w.im := by simpa only [hw,div_one] using Complex.sin_arg w
      rw [hz,Real.sin_zero] at hs
      exact hIm.ne' hs.symm
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hθπ : Complex.arg w<Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hIm.ne')
  have hcanon : w=(Real.cos (Complex.arg w) : ℂ)+Real.sin (Complex.arg w)*Complex.I := by
    simpa only [hw,Complex.ofReal_one,one_mul,← Complex.ofReal_cos,← Complex.ofReal_sin] using
      (Complex.norm_mul_cos_add_sin_mul_I w).symm
  have hmasses := positivePlanarWedge_gaussian_mass_isometry L u v
  rw [hLu,show L v=w from rfl,hcanon,positivePlanarWedge_canonical_gaussian_mass _ hθ0 hθπ] at hmasses
  have hi : ⟪u,v⟫_ℝ=w.re := by
    rw [← L.inner_map_map u v,hLu,Complex.inner]
    simp only [map_one,mul_one]
    rfl
  rw [← hmasses,Complex.arg_of_im_pos hIm,hw,div_one,hi]

theorem positivePlanarWedge_complex_angular_area (u v : ℂ) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hp : u+v≠0) (hm : u-v≠0) :
    (volume : Measure ℂ).toSphere.real (supplementalHSphericalSection (positivePlanarWedge u v))=
      Real.arccos ⟪u,v⟫_ℝ := by
  rw [← supplementalH_planar_cone_gaussian_mass volume Complex.finrank_real_complex _
    (positivePlanarWedge_complex_measurable u v hu hv hp hm)
    (fun r hr z => positivePlanarWedge_dilation u v r hr z)]
  exact positivePlanarWedge_complex_gaussian_mass u v hu hv hp hm

/-- Angular area transport through a genuine Euclidean-plane isometry.
This applies directly to a two-dimensional tangent subspace. -/
theorem positivePlanarWedge_angular_area_of_isometry {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (L : E ≃ₗᵢ[ℝ] ℂ) (hdim : Module.finrank ℝ E=2)
    (u v : E) (hu : ‖u‖=1) (hv : ‖v‖=1) (hp : u+v≠0) (hm : u-v≠0) :
    (volume : Measure E).toSphere.real (supplementalHSphericalSection (positivePlanarWedge u v))=
      Real.arccos ⟪u,v⟫_ℝ := by
  have hLu : ‖L u‖=1 := (L.norm_map u).trans hu
  have hLv : ‖L v‖=1 := (L.norm_map v).trans hv
  have hLp : L u+L v≠0 := by
    intro hz
    apply hp
    apply L.injective
    simpa only [map_add,map_zero] using hz
  have hLm : L u-L v≠0 := by
    intro hz
    apply hm
    apply L.injective
    simpa only [map_sub,map_zero] using hz
  have hc := (positivePlanarWedge_complex_measurable (L u) (L v) hLu hLv hLp hLm).preimage
    L.continuous.measurable
  rw [← positivePlanarWedge_isometry_image L u v,Set.preimage_image_eq _ L.injective] at hc
  rw [← supplementalH_planar_cone_gaussian_mass volume hdim _ hc
    (fun r hr z => positivePlanarWedge_dilation u v r hr z),
    ← positivePlanarWedge_gaussian_mass_isometry L u v,
    positivePlanarWedge_complex_gaussian_mass (L u) (L v) hLu hLv hLp hLm,
    L.inner_map_map]

/-- The angular area of the actual positive cone generated by two
nonparallel unit endpoint rays is their ordinary angle, on any Euclidean
plane including a two-dimensional subspace of a larger ambient space. -/
theorem positivePlanarWedge_angular_area {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (hdim : Module.finrank ℝ E=2) (u v : E)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (hp : u+v≠0) (hm : u-v≠0) :
    (volume : Measure E).toSphere.real (supplementalHSphericalSection (positivePlanarWedge u v))=
      Real.arccos ⟪u,v⟫_ℝ := by
  let b : OrthonormalBasis (Fin 2) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  let L : E ≃ₗᵢ[ℝ] ℂ := b.repr.trans Complex.orthonormalBasisOneI.repr.symm
  exact positivePlanarWedge_angular_area_of_isometry L hdim u v hu hv hp hm

end
end RectangleCLTArxivV1
