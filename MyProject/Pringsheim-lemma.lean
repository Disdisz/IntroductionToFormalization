

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


example (f: ℕ → ℂ ) (t := Finset.range 1) :
    ∑' x , f x = f 0:= by sorry

example (f : ℕ → ℕ → ℂ ) (m : ℕ ) :
    --∑ n ∈ (Finset.range m), ∑ k ∈ (Finset.range n), f k
    (Finset.range m).sum (λ i => (Finset.range (i + 1) ).sum (λ j => f i j))
    = (Finset.range m).sum (λ j => (Finset.Ico j m ).sum (λ j => f i j)) := by
    --rw [Finset.sum_comm]
  -- Now we are summing over j ∈ range m, i ∈ Icc j (m - 1)
  -- because originally j ≤ i < m, so i ∈ [j, m)
    --rfl
    sorry
    -- simp only [Finset.range, Finset.sum_insert, Finset.not_mem_range_self] -- i = 0, 1, 2

    -- simp only [Multiset.range_succ, Multiset.range_zero, Multiset.cons_zero, Finset.mk_cons,
    --   Finset.cons_eq_insert, Finset.sum_mk, Finset.mem_insert, OfNat.ofNat_ne_one, Finset.mem_mk,
    --   Multiset.mem_singleton, OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert,
    --   Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton,
    --   one_ne_zero, Multiset.map_zero, Multiset.sum_zero, add_zero]-- only [Finset.range_zero, Finset.sum_empty]  -- i = 0 \u2192 sum is 0
    -- ring



open Finset BigOperators

def I : Finset ℕ := {0, 1, 2}

def J (i : ℕ) : Finset ℕ := {0, 1, 2}

def f (i j : ℕ) : ℕ := i + j

def result : ℕ := I.sum (λ i => (J i).sum (λ j => f i j))

#eval result  -- Output: 27



lemma sumform (z : ℂ  ) {φ :  ℂ → ℂ }
    {μ : ℝ }
    {ser_at_ρ : FormalMultilinearSeries ℂ ℂ ℂ }
    {ε : ENNReal}
    (has_ser_on_ball : HasFPowerSeriesOnBall φ ser_at_ρ ↑μ (2 / 3 * ε))
    : (↑z : ℂ) ∈ EMetric.ball 0 (2/3 * ε ) →    φ (↑μ + ↑z) = (∑' (b : ℕ), ((1 : ℝ)  / ↑(b.factorial)) • (iteratedFDeriv ℂ b φ ↑μ) fun _ ↦ ↑z)  := by--2 := by--∑' n, (fun n ↦ ((1 : ℝ)  / ↑(n.factorial)) • (iteratedFDeriv ℂ n φ ↑μ)) := by
    intro hz
    apply has_ser_on_ball.hasSum_iteratedFDeriv at hz
    apply HasSum.tsum_eq at hz
    simp only [hz.symm, smul_eq_mul, one_div, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_natCast]          --tää on sus koska riippuu siitä, miten nimesin b:n


example (l μ : ℝ ) : ‖l + μ‖ₑ ≤ ‖l‖ₑ + ‖μ‖ₑ := by
    exact ENormedAddMonoid.enorm_add_le l μ

lemma dist_tri (l μ ρ : ℝ ) : ‖l - μ‖ₑ ≤ ‖l-ρ‖ₑ + ‖ρ-μ‖ₑ := by
    rw [(by simp only [sub_add_sub_cancel] : l - μ = (l - ρ) + (ρ - μ))]
    exact ENormedAddMonoid.enorm_add_le (l - ρ) (ρ - μ)

lemma switch_order (r: ℝ ) : r = 0 := by
    sorry

open scoped BigOperators
open Complex

lemma nth_deriv_of_series(r: ENNReal)  (hr: r > 0) (φ : ℂ → ℂ ) (b: ℕ ) (a : ℝ  ) --(hφ : AnalyticAt ℂ φ 0)
    --(h_real : ∀ n : ℕ , (hφ.choose.coeff n).im = 0)
    --(h_pos : ∀ n : ℕ , (hφ.choose.coeff n).re ≥ 0)
    --(h_rad_pos_fin : hφ.choose.radius.toReal > 0)  --ehkä tämä toiseen muotoon (pos oletus pois tästä koska on jo analyticatissa)
    (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
    (on_ball_at_a  : HasFPowerSeriesOnBall φ ser_at_0 0 r)
    (ha : (↑a : ℂ ) ∈ EMetric.ball 0 r)

    --(φ a = ∑' (b : ℕ), (1 / ↑b.factorial) • (iteratedFDeriv ℂ b φ a) fun x ↦ 0)
    : (iteratedFDeriv ℂ b φ a) (fun x ↦ a) = ∑' m, a ^m * ser_at_0.coeff (m + b) * ((m + b).factorial/m.factorial)   := by
    induction b
    ·   simp only [iteratedFDeriv_zero_apply, add_zero]
        have obv : (a : ℂ ) ∈ EMetric.ball 0 r := by sorry
        apply on_ball_at_a.hasSum at obv
        have now : (∑' n, (ser_at_0 n) fun x ↦ a )= (φ (0 + a)) := by
            exact HasSum.tsum_eq obv
        simp at now
        rw [<- now]
        have eq_one (n: ℕ): ((↑n.factorial : ℂ ) / (↑n.factorial: ℂ )) = 1 := by
            refine (div_eq_one_iff_eq ?_).mpr rfl
            rewrite [Nat.cast_ne_zero]
            exact Nat.factorial_ne_zero n
        conv in (↑n.factorial / ↑n.factorial) =>
            rw [eq_one m]
        simp only [mul_one]
    ·   --levita iteratedfderiv
        --apply ass
        --pitäis toimia
        sorry
    --rw [HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace on_ball_at_μ]

    -- have  ∑' (n : ℕ), ser_at_ρ.coeff (n + b) * ↑(n + b).factorial / ↑n.factorial * a ^ n
    --     apply tsum_congr

    -- by_cases h : k < b
    -- · simp [h]
    -- · push_neg at h
    --     let n := k - b
    --     have : k = n + b := by rw [Nat.add_sub_of_le h]
    --     rw [this]
    --     simp only [this, zero_add]
    --     -- symmetry of coefficients lets us assume all `a`s at the end
    --     congr 1
    --     -- `ser_at_ρ (n + b) (λ i ↦ if i < n then 0 else a) = ser_at_ρ.coeff (n + b) * a^n`
        -- requires `ser_at_ρ` to be symmetric (which it is)
        -- So, apply the definition of symmetric multilinear maps on repeated variables
    --sorry

    --rw [ContinuousMultilinearMap.iteratedFDeriv_eq φ b]
    --#check HasFPowerSeriesOnBall.hasFPowerSeriesOnBall_iteratedFDeriv
    --#check on_ball_at_μ.iteratedFDeriv_eq_sum_of_completeSpace
    --nth_rewrite 1 [on_ball_at_μ.iteratedFDeriv_eq_sum_of_completeSpace]
    -- simp only [
    --     --prod_const,
    --     card_univ,
    --     --FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    --     Fintype.card_fin,
    --     --smul_eq_mul,
    --     sum_const,
    --     nsmul_eq_mul,
    --     Fintype.card_perm]
    -- have now : (a ^ b * ser_at_ρ.coeff b) = 1 := by

       -- sorry
    -- have permutations_fac : Fintype.card (Equiv.Perm (Fin b)) = b.factorial := by
    --     rewrite [Fintype.card_perm]
    --     simp
    --have moii :=  on_ball_at_μ.iteratedFDeriv_eq_sum_of_completeSpace








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
    have ε'_pos : ε' > 0 := by exact h_series.r_pos
    have obvious : HasFPowerSeriesOnBall φ ser_at_ρ ↑ρ (min ε' ρ.toNNReal) :=
        {
            r_le := usein,
            r_pos := by
                simp only [lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos]
                exact ⟨ε'_pos, h_rad_pos_fin⟩,
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

                --#check obvious.hasSum

                sorry
        }

    let l : ℝ := ρ + ε.toReal / 4
    let l' := l - μ
    have l_le_bord : l < ρ + ε.toReal / 3 := by
        refine (Real.add_lt_add_iff_left ρ).mpr (div_lt_div_of_pos_left ε_pos ?_ ?_  )
        repeat norm_num
    have l'_in_bμ : (l' : ℂ) ∈ EMetric.ball 0 (2 / 3 * ε) := by
        simp only [EMetric.mem_ball, edist_zero_right]
        unfold l'
        have simplification : ‖l - μ‖ₑ.toReal = |l - μ| := by rfl
        have ε_ne_zero : ε.toReal ≠ 0 :=  Ne.symm (ne_of_lt ε_pos) --turha
        have ε_ne_top : ε ≠ ⊤ := by
            exact Ne.symm (ne_of_apply_ne ENNReal.toReal fun a ↦ ε_ne_zero (id (Eq.symm a))) --ENNReal.toReal_ne_zero
        have not_top : ‖l - μ‖ₑ ≠ ⊤ := by exact enorm_ne_top
        sorry
        -- rewrite [<- ENNReal.toReal_lt_toReal not_top]--ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ]
        -- ·   rewrite [simplification]
        --     simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat]
        --     rewrite [(by simp only [sub_add_sub_cancel]: |l- μ| = |(l-ρ) + (ρ-μ)|)]
        --     --TODO:
        --     --lt_of_le_of_lt kolmio + oikean jako kahteen
        --     sorry
        -- ·   refine ENNReal.mul_ne_top ?_ ε_ne_top
        --     refine not_isMax_iff_ne_top.mp ?_
        --     unfold IsMax
        --     push_neg
        --     use 1
        --     exact ⟨by ---upcastauksen kautta
        --         ---VITTU
        --         sorry
        --         , by
        --         --norm_num
        --         sorry
        --         ⟩
        --     --refine ENNReal.inv_ne_zero.mp ?_
              ---TODO why is this necessary
    -- have zero_in_ball : (0 : ℂ )  ∈ EMetric.ball 0 (2 / 3 * ε) := by
    --     simp
    --     exact obvious.r_pos
    -- have sum_at_μ := sumform 0 has_pow_at_μ zero_in_ball

    have sum_at_l := sumform l' has_pow_at_μ l'_in_bμ
    let α := μ / ρ
    have α_lt_1 : α < 1 := by sorry
    let δ := (ρ - ε.toReal/3) / μ  - 1
    have δ_pos : δ > 0 := by sorry
    clear usein
    clear obvious
    clear l_le_bord
    clear l'_in_bμ
    --uusin pohdinta: missä on potenssihomma? (= mikä on iteratedFDeriv)
    have derivaattamuokkaus (n: ℕ):= nth_deriv_of_series
        (ENNReal.ofReal ρ)
        (by exact ENNReal.ofReal_pos.mpr h_rad_pos_fin)
        (φ)
        (n)
        (μ)
        (hφ.choose)
        (by sorry)  --simlpe
        (by sorry)  --simple



    --have final_sum : summable?∑' sorry := by sorry


    have analytic_at_too_far : AnalyticAt ℂ φ ↑(ρ + ε.toReal/4) := by sorry
    have size_ρplus : (↑|ρ  + ε.toReal/4| : ℂ ) = ρ + ε.toReal/4 := by sorry
    --formal_multilinear_series.not_summable_norm_of_radius_lt_nnnorm
    --exact?
    sorry


    lemma sarjayritys : 1 = 1 := by sorry



    theorem katko
        (φ : ℂ → ℂ)
        (hφ : AnalyticAt ℂ φ 0)
        (h_real : ∀ (n : ℕ), ((Exists.choose hφ).coeff n).im = 0)
        (h_pos : ∀ (n : ℕ), ((Exists.choose hφ).coeff n).re ≥ 0)
        (h_rad_pos_fin : (Exists.choose hφ).radius.toReal > 0)
        (ρ : ℝ := (Exists.choose hφ).radius.toReal)
        (ser_at_ρ : FormalMultilinearSeries ℂ ℂ ℂ)
        (ε' : ENNReal)
        (h_series : HasFPowerSeriesOnBall φ ser_at_ρ (↑(Exists.choose hφ).radius.toReal) ε')
        (usein : min ε' ↑ρ.toNNReal ≤ ser_at_ρ.radius)
        (ε'_pos : ε' > 0)
        (obvious : HasFPowerSeriesOnBall φ ser_at_ρ (↑ρ) (min ε' ↑ρ.toNNReal))
        (ε : ENNReal := min ε' ↑ρ.toNNReal)
        (ε_pos : 0 < ε.toReal)
        (μ : ℝ := ρ - ε.toReal / 3)
        (has_pow_at_μ : HasFPowerSeriesOnBall φ ser_at_ρ (↑μ) (2 / 3 * ε))
        (l : ℝ := ρ + ε.toReal / 4)
        (l' : ℝ := l - μ)
        (l_le_bord : l < ρ + ε.toReal / 3)
        (l'_in_bμ : ↑l' ∈ EMetric.ball 0 (2 / 3 * ε))
        (sum_at_l : φ (↑μ + ↑l') = ∑' (b : ℕ), (1 / ↑b.factorial) • (iteratedFDeriv ℂ b φ ↑μ) fun x ↦ ↑l')
        : False := by
        let α := μ / ρ

        sorry


    --def taylorCoeff f z₀ n := (Analysis.Calculus.iterated_deriv ℂ  n f z₀ ) / (n.factorial : ℂ )


    -- example (hf : AnalyticAt ℂ f z₀) :
    -- ∃ r > 0, ∀ z ∈ EMetric.ball z₀ r, f z = ∑' n, (iteratedDeriv n f z₀ ) / (n.factorial : ℂ ) * (z-z₀)^n := by
    --     rcases hf.hasFPowerSeriesAt with ⟨r, hconv⟩
    --     use r, hconv.r_pos
    --     intro z hz
    --     apply hconv.hasSum at hz



    --     --unfold HasSum at hz

    --     --#check hconv.hasSum

    --     --exact hz


    -- --have ε_fin : ε < hφ.choose.radius := by exact h_series.r_le

    -- --rename_bvar (Exists.choose hφ).radius.toReal ρ at *


    --     sorry

    -- --Complex.taylorSeries_eq_on_ball'








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
