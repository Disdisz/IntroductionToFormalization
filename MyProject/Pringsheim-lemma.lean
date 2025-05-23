import Mathlib

import Mathlib.Data.Complex.Basic

--yksi implementaatio:
variable {a : ℕ → ℝ }
def ha := a > 0

noncomputable def φ : ℂ  →  ℂ := fun l ↦ ∑' i, (l ^ i * a i)

--tömö mutta sitten pitää näyttää että fii on formalmultilinearseries
--radius of convergence (∈ (0, ))








--toinen implementaatio:

-- variable {φ : ℂ → ℂ } {hφ : (AnalyticAt ℂ φ 0)}
--     --{h_pos : ∀ n : ℕ , hφ.choose.coeff n = |(hφ.choose.coeff n).re|}
--     {h_real : ∀ n : ℕ , (hφ.choose.coeff n).im = 0}
--     {h_pos : ∀ n : ℕ , (hφ.choose.coeff n).re ≥ 0}
--     {h_rad_pos_fin : hφ.choose.radius.toReal > 0}
--     --{h_rad_fin : hφ.choose.radius < (infty : ENNReal) }
--     --{m : ℕ  }
-- noncomputable def ρ : ℝ  := hφ.choose.radius.toReal


--lemma obvious? : --(h : HasFPowerSeriesOnBall )
lemma obvious' (φ : ℂ → ℂ ) (hφ : AnalyticAt ℂ φ 0)
    (h_neg : AnalyticAt ℂ φ (Complex.ofReal hφ.choose.radius.toReal))
    : ∃ser : FormalMultilinearSeries ℂ ℂ ℂ, ∃ε : ENNReal ,
        ε ≤ hφ.choose.radius ∧       --tätä ei periaatteessa tarvita, mutta tällä hetkellä tuntuu, että se ehkä helpottaa asioita.
        HasFPowerSeriesOnBall φ ser ↑hφ.choose.radius.toReal ε:= by
    let ρ  := hφ.choose.radius
    unfold AnalyticAt at h_neg
    cases' h_neg with ser_at_ρ h_ser_at_ρ
    unfold HasFPowerSeriesAt at h_ser_at_ρ
    cases' h_ser_at_ρ with ε' h_series
    have ε_pos : ε' > 0 := by exact h_series.r_pos
    have main : HasFPowerSeriesOnBall φ ser_at_ρ ↑ρ.toReal (min ε' ρ) :=
        {
            r_le := le_trans (min_le_left ε' ρ) h_series.r_le,
            r_pos := by
                simp only [lt_inf_iff, ENNReal.coe_pos]-- only [lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos]
                exact ⟨ε_pos, hφ.choose_spec.radius_pos⟩,
            hasSum := by
                intro y hy
                have biggerBall : y ∈ EMetric.ball 0 ε' := by
                    exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left ε' ρ))
                apply h_series.hasSum at biggerBall
                exact biggerBall
        }
    use ser_at_ρ
    use (min ε' ρ)
    exact ⟨by
        simp only [inf_le_iff]
        right
        exact Preorder.le_refl ρ
        , main⟩


lemma sumform {φ :  ℂ → ℂ }
    {μ : ℝ }
    {ser_at_ρ : FormalMultilinearSeries ℂ ℂ ℂ }
    {ε : ENNReal}
    (has_ser_on_ball : HasFPowerSeriesOnBall φ ser_at_ρ ↑μ (2 / 3 * ε))
    : ∀ z ∈ EMetric.ball 0 (2/3 * ε ),  φ (↑μ + z) = (∑' (b : ℕ), ((1 : ℝ)  / ↑(b.factorial)) • (iteratedFDeriv ℂ b φ ↑μ) fun x ↦ z)  := by--2 := by--∑' n, (fun n ↦ ((1 : ℝ)  / ↑(n.factorial)) • (iteratedFDeriv ℂ n φ ↑μ)) := by
    intro z hz
    apply has_ser_on_ball.hasSum_iteratedFDeriv at hz
    apply HasSum.tsum_eq at hz
    simp only [hz.symm, smul_eq_mul, one_div, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_natCast]          --tää on sus koska riippuu siitä, miten nimesin b:n


--hada martin
theorem pringsheim (φ : ℂ → ℂ ) (hφ : AnalyticAt ℂ φ 0)
    (h_real : ∀ n : ℕ , (hφ.choose.coeff n).im = 0)
    (h_pos : ∀ n : ℕ , (hφ.choose.coeff n).re ≥ 0)
    (h_rad_pos_fin : hφ.choose.radius.toReal > 0)  --ehkä tämä toiseen muotoon (pos oletus pois tästä koska on jo analyticatissa)
    : ¬(AnalyticAt ℂ φ (Complex.ofReal hφ.choose.radius.toReal)) := by
    let ρ : ℝ  := hφ.choose.radius.toReal
    by_contra hmoi
    unfold AnalyticAt at hmoi
    cases' hmoi with ser_at_ρ h_ser_at_ρ
    unfold HasFPowerSeriesAt at h_ser_at_ρ
    cases' h_ser_at_ρ with ε' h_series
    unfold HasFPowerSeriesOnBall at h_series
    have usein := le_trans (min_le_left ε' ↑ρ.toNNReal) h_series.r_le
    have ε_pos : ε' > 0 := by exact h_series.r_pos
    have obvious : HasFPowerSeriesOnBall φ ser_at_ρ ↑ρ (min ε' ρ.toNNReal) :=
        {
            r_le := usein,
            r_pos := by
                simp only [lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos]
                exact ⟨ε_pos, h_rad_pos_fin⟩,
            hasSum := by
                intro y hy
                have biggerBall : y ∈ EMetric.ball 0 ε' := by
                    exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left ε' ↑ρ.toNNReal))
                apply h_series.hasSum at biggerBall
                exact biggerBall
        }
    let ε := (min ε' ρ.toNNReal)
    have ε_pos : 0 < ε.toReal := by sorry   --we know this is true
    let μ := ρ - (ε.toReal / 3)
    have has_pow_at_μ : HasFPowerSeriesOnBall φ ser_at_ρ ↑μ (2 / 3 * ε) := by
        exact {
            r_le := by
                have first : 2 / 3  * ε ≤ ε := by sorry  --THIS SHOULD BE TRIVIAL
                exact le_trans first usein
            r_pos := by
                norm_num
                exact obvious.r_pos
            hasSum := by
                have reformulation : ∀ y : ℂ, y ∈ EMetric.ball 0 (min ε' ↑ρ.toNNReal) →
                    HasSum (fun n ↦ (ser_at_ρ n) fun x ↦ y) (φ (↑ρ + y))  := by
                    intro y hy
                    exact obvious.hasSum hy
                intro y hy
                --have check : y =
                --have in_bigger_ball :  ∈ EMetric.ball 0 ε := by sorry

                #check obvious.hasSum

                sorry
        }
    -- have analytic_at_μ : AnalyticAt ℂ φ ↑μ := by
    --     use ser_at_ρ, 2 / 3 * ε
    have taylorsum := sumform has_pow_at_μ
    let l : ℝ := ρ + ε.toReal / 4
    let l' := l - μ
    have l_le_bord : l < ρ + ε.toReal / 3 := by
        refine (Real.add_lt_add_iff_left ρ).mpr (div_lt_div_of_pos_left ε_pos ?_ ?_  )
        repeat norm_num
    have l'_in_bμ : l' ∈ EMetric.ball 0 (2 / 3 * ε) := by
        simp only [EMetric.mem_ball, edist_zero_right]

        sorry
    --apply has_pow_at_μ.hasSum_iteratedFDeriv
    --#check AnalyticAt.hasFPowerSeriesAt
    #check HasFPowerSeriesOnBall.hasSum_iteratedFDeriv--hasFPowerSeriesWithinOnBall
    --#check HasFPowerSeriesWithinOnBall

    sorry




    --def taylorCoeff f z₀ n := (Analysis.Calculus.iterated_deriv ℂ  n f z₀ ) / (n.factorial : ℂ )


    example (hf : AnalyticAt ℂ f z₀) :
    ∃ r > 0, ∀ z ∈ EMetric.ball z₀ r, f z = ∑' n, (iteratedDeriv n f z₀ ) / (n.factorial : ℂ ) * (z-z₀)^n := by
        rcases hf.hasFPowerSeriesAt with ⟨r, hconv⟩
        use r, hconv.r_pos
        intro z hz
        apply hconv.hasSum at hz



        --unfold HasSum at hz

        --#check hconv.hasSum

        --exact hz


    --have ε_fin : ε < hφ.choose.radius := by exact h_series.r_le

    --rename_bvar (Exists.choose hφ).radius.toReal ρ at *


        sorry

    --Complex.taylorSeries_eq_on_ball'








--def h_pos := hφ.choose

--power series muoto (from anaytic?)

--radius of convergence

--nonneg real coeff

















--kolmas implementaatio:
variable {a : FormalMultilinearSeries ℝ ℂ  ℂ } --{a_pos : ∀n : ℕ , a n 1 ≥ 0} --TODO: miten joukot menee
--noncomputable def rho := a.radius



--#check

example : 1 + 1 = 2 := by
    --let moi := hφ.choose
    --let moi2 := moi.coeff
    --let h : ∀ n : ℕ , moi2 n ∈ reals = sorry
    --unfold FormalMultilinearSeries at a
    -- let moi := a 0
    -- unfold ContinuousMultilinearMap at a
    sorry

variable {m : ℝ }

--

--#check R

--#check Summable a

--def φ : ℂ → ℂ := ∑


--miten nimeän φ:lle radius of convergencen?

--

--analyyttinen ↔ potenssisarjamääritelmä suppenee
