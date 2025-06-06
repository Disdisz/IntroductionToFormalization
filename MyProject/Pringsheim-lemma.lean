

import Mathlib



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

--variable (f: ℕ → ℕ → ℂ )
def γ : ℕ → Set ℕ := fun b' => Set.Icc 0 b'
def δ : ℕ → Set ℕ := fun b' => Set.Ici b'


--noncomputable def sigma := ∑' (b: ℕ ) (c : γ b), f b c


-- Let A be any type, and B : A → Type
variable {A : Type} {B : A → Type}

-- The sigma type
def sig : Type := Σ x : A, B x

-- We want to interpret this as a subset of a product type
-- Let's define a dependent predicate over A × (Σ x, B x) → Prop
def sigma_to_subset : (A × (Σ x, B x)) → Prop :=
  λ p => ∃ (b : B p.1), p.2 = ⟨p.1, b⟩



--I originally generated this using chatgpt and then (heavily) modified
example (f: (b: ℕ ) × γ b → ℂ ) (g : (k : ℕ ) × δ k → ℂ ) (hf: Summable f) (hg: Summable g)
  (f_eq_g : ∀ (p : (b: ℕ ) × γ b  ) (p2 : (k : ℕ ) × δ k ), p.1 = ↑p2.2 ∧ ↑p.2 = p2.1 → f p = g p2 ):
  ∑' (b : ℕ ) (k : γ b), f ⟨b ,  k⟩ = ∑' (k : ℕ) (b : δ k), g ⟨k, b⟩ := by
  rewrite [<- Summable.tsum_sigma hf, <- Summable.tsum_sigma hg]
  let equ : (Σ b, γ b) ≃ (Σ k, δ k) :=
    { toFun := λ ⟨b, y⟩ => ⟨↑y, ⟨ b, by
        -- unfold δ
        -- unfold Set.Ici
        -- unfold γ at y
        -- unfold Set.Icc at y
        refine Set.mem_setOf.mpr y.property.2⟩ ⟩
      invFun := λ ⟨k, x⟩ => ⟨↑x, ⟨k, by
        -- unfold δ at x
        -- unfold Set.Ici at x
        -- unfold γ
        -- unfold Set.Icc
        constructor
        · simp only [zero_le]
        · exact Set.mem_setOf.mpr x.property
        ⟩⟩
      left_inv := by
        rintro ⟨b, y⟩
        simp only
      right_inv := by
        rintro ⟨k, x⟩
        simp only
    }
  have equ' : Function.support f ≃ Function.support g := by sorry   --less strict formulations for equ
  have f_eq_g' :  ∀ (x : ↑(Function.support f)), g ↑(equ' x) = f ↑x := by sorry -- l. s. form. for f_eq_g
  exact @Equiv.tsum_eq_tsum_of_support ℂ ((b: ℕ ) × γ b) ((k : ℕ ) × δ k) _ _ _ _ equ' f_eq_g'

  -- apply tsum_eq_tsum_of_hasSum_hasSum'
  -- exact hf.hasSum
  -- exact hg.hasSum
  -- intro p
  -- specialize f_eq_g (e.symm p) p
  -- simp only at f_eq_g
  -- rw [f_eq_g]
  -- simp only [e]
  -- rfl
  -- constructor
  -- · exact rfl
  -- · exact rfl


--Ok so:
--we have to change the two sums inside eachother to that ^^^^ form
--then we have to change back

example --(f: (b: ℕ ) × γ b → ℂ )
  :  ∑' (b : ℕ), ∑' (k : γ b), (fun b' : ℕ  ↦ (fun k' ↦ b' * k')) b k  = ∑' (b : ℕ ) (k : γ b), b * k := by
  simp only



--example (f: (b: ℕ ) × γ b → ℂ ) (f' : )






example (f: (b: ℕ ) × γ b → ℂ ) (g : (k : ℕ ) × δ k → ℂ ) (hf: Summable f) (hg: Summable g)
  (f_eq_g : ∀ (p : (b: ℕ ) × γ b  ) (p2 : (k : ℕ ) × δ k ), p.1 = ↑p2.2 ∧ ↑p.2 = p2.1 → f p = g p2 ):
  ∑' (b : ℕ ) (k : γ b), f ⟨b ,  k⟩ = ∑' (k : ℕ) (b : δ k), g ⟨k, b⟩ := by
  rewrite [<- Summable.tsum_sigma hf, <- Summable.tsum_sigma hg]
  --apply sigma_to_subset
  sorry

example (f: (ℕ × ℕ ))

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


--TODO:
-- lopetus
-- äskeisten lauseiden applikointi
-- derivaattajutussa ehkä vielä jotain
-- siistiminen



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


lemma dist_tri (l μ ρ : ℝ ) : ‖l - μ‖ₑ ≤ ‖l-ρ‖ₑ + ‖ρ-μ‖ₑ := by
  rw [(by simp only [sub_add_sub_cancel] : l - μ = (l - ρ) + (ρ - μ))]
  exact ENormedAddMonoid.enorm_add_le (l - ρ) (ρ - μ)



open Function Set
--we need a lemma stating that f.uncurry is summble when f is twice summable
lemma switch_order (f : ℕ → ℕ → ℂ ) (hf : Summable (Function.uncurry fun j i ↦ {x | ∃ i ≤ j, (i, j) = x}.indicator (Function.uncurry f) (i, j)))
  : ∑' (i : ℕ ) (j: ℕ ), {(i, j) | i ≤ j }.indicator (f.uncurry) (i , j) = ∑' (j : ℕ) (i : ℕ ), {(i, j) | i ≤ j }.indicator (f.uncurry) (i , j):= by
  refine Summable.tsum_comm' ?_ ?_ ?_
  · exact hf
  · intro b
    have fin : Set.Finite {x | ∃ i ≤ b, (i, b) = x} := by
      sorry
    unfold Summable
    --use Finset.sum {x | ∃ i ≤ b, (i, b) = x} (Function.uncurry f)
    --clearly this is true but slightly painful
    sorry
  · intro c
    have right? : (Function.uncurry fun j i ↦ {x | ∃ i ≤ j, (i, j) = x}.indicator (Function.uncurry f) (i, j)) =  { (i, j)  : (ℕ × ℕ ) |  i ≤ j}.indicator (Function.uncurry f) := by
      ext x
      simp only [indicator, mem_setOf_eq, Prod.mk.injEq, and_true, exists_eq_right, uncurry]
      cases x with
      | mk i j =>


      · simp!
        sorry
      · sorry

    sorry

lemma exp_form (n : ℕ) (f :  ℂ [×n]→L[ℂ ] ℂ )--ContinuousMultilinearMap ℂ (fun i ↦ ℂ) ℂ)
  (l : ℂ ) :
  f (fun x ↦ l) = f (fun x ↦ 1)  * l^n  := by
  · let c' := f (fun x ↦ 1)
    let c : Fin n → ℂ := fun x ↦ l
    let m : Fin n → ℂ := fun x ↦ 1
    have slighty_easier_form
    : (f fun (i : (Fin n)) => c i • m i) = (∏ i : (Fin n), c i) • f m := by
      exact ContinuousMultilinearMap.map_smul_univ f c m
    simp only [smul_eq_mul] at *
    unfold m at slighty_easier_form
    unfold c at slighty_easier_form
    simp at *
    rewrite [slighty_easier_form]
    exact CommMonoid.mul_comm (l ^ n) (f fun x ↦ 1)





-- lemma change_fun_alku (f g : ℂ → ℂ ) (s : Set ℂ ) (h : EqOn f g s) --(x : ℂ ) (hx : x ∈ s) --saattaa olla turha
-- : EqOn (derivWithin f s) (derivWithin g s) s := by
--   unfold EqOn
--   intro a ha
--   have heq : f a = g a := by exact h ha
--   rw [derivWithin_congr h heq]

lemma chagne_fun_loppu (a : ℂ ) (f g : ℂ → ℂ ) (s : Set ℂ ) (h : EqOn f g s)  (ha : a ∈ s)--(heq : EqOn (derivWithin f s) (derivWithin g s) s) (ha : a ∈ s)
: derivWithin f s a = derivWithin g s a := derivWithin_congr h (h ha)


--shoud be lyhennettävissä
lemma simplifying_of_deriv (a : ℂ ) (r : ENNReal) (b' : ℕ ) (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (u : ℕ → ℝ )  (ha : a ∈ (EMetric.ball 0 r) )
  (hu : Summable u)
  (hg : ∀ (n : ℕ ), Differentiable ℂ (fun (a : ℂ) ↦ a ^ n * ser_at_0.coeff (n + b') * (↑(n + b').factorial / ↑n.factorial) ) )
  (hg' : ∀ (n : ℕ ) (y : ℂ), ‖deriv ( fun (a : ℂ) ↦ a ^ n * ser_at_0.coeff (n + b') * (↑(n + b').factorial / ↑n.factorial)) y‖ ≤ u n)
  ( hg0 : Summable fun (n : ℕ ) =>  a ^ n * ser_at_0.coeff (n + b') * (↑(n + b').factorial / ↑n.factorial))
: derivWithin (fun a ↦ ∑' (m : ℕ), a ^ m * ser_at_0.coeff (m + b') * (↑(m + b').factorial / ↑m.factorial))
    (EMetric.ball 0 r) a =
  ∑' (m : ℕ), a ^ m * ser_at_0.coeff (m + (b' + 1)) * ((↑m + ↑b' + 1) * ↑(m + b').factorial / ↑m.factorial)
  := by
  have ball_open : IsOpen (EMetric.ball (0 : ℂ) r) := by exact EMetric.isOpen_ball
  rewrite [derivWithin_of_isOpen ball_open ha, deriv_tsum_apply hu hg hg' hg0]
  simp only [deriv_mul_const_field', differentiableAt_id', DifferentiableAt.pow,
    differentiableAt_const, deriv_mul, deriv_pow'', deriv_id'', mul_one, deriv_const', mul_zero,
    add_zero]
  have  hf : Summable (fun n ↦ ↑n * a ^ (n - 1) * ser_at_0.coeff (n + b') * (↑(n + b').factorial / ↑n.factorial))
    := by sorry
  rewrite [Summable.tsum_eq_zero_add hf] --pitää edetä toisesta suunnasta sittenkin kun toinen on summable
  simp only [CharP.cast_eq_zero, zero_tsub, pow_zero, mul_one, zero_add, zero_mul,
    Nat.factorial_zero, Nat.cast_one, div_one, Nat.cast_add, add_tsub_cancel_right]
  apply tsum_congr
  intro n
  --simp!
  calc
    (↑n + 1) * a ^ n * ser_at_0.coeff (n + 1 + b') * (↑(n + 1 + b').factorial / ↑(n + 1).factorial) =
      a ^ n * ser_at_0.coeff (n + 1 + b') * (↑n + 1) *(↑(n + 1 + b').factorial / ↑(n + 1).factorial)
      := by ring
    a ^ n * ser_at_0.coeff (n + 1 + b') * (↑n + 1) *(↑(n + 1 + b').factorial / ↑(n + 1).factorial)
      =  a ^ n * ser_at_0.coeff (n + 1 + b') * ↑(n + 1 + b').factorial * (↑n + 1)  / ↑(n + 1).factorial
      := by ring
    a ^ n * ser_at_0.coeff (n + 1 + b') * ↑(n + 1 + b').factorial * (↑n + 1)  / ↑(n + 1).factorial
      = a ^ n * ser_at_0.coeff (n + 1 + b') * ↑(n + 1 + b').factorial / ↑n.factorial
      := by
        have lol (n: ℕ) : (n + 1) / (n + 1).factorial  = 1 / (↑n.factorial : ℂ ) := by
          simp! only []  --sus
          simp only [Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          --should be trivial
          sorry
        rw [(lol n)] -- shoul nbe trivial
        sorry

  sorry --this is also clearly true





lemma nth_deriv_of_series_valivaihe(r: ENNReal)  (hr: r > 0) (φ : ℂ → ℂ ) (b: ℕ ) --(a : ℝ  ) --(hφ : AnalyticAt ℂ φ 0)
  (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (on_ball_at_0  : HasFPowerSeriesOnBall φ ser_at_0 0 r)
 -- (ha : (↑a : ℂ ) ∈ EMetric.ball 0 r) --perkele, tää pitää ehkä muuttaa kuitenkin abstraktimmaksi
  :EqOn (iteratedDerivWithin b φ (EMetric.ball 0 r)) ( fun a ↦ (∑' m, a ^m * ser_at_0.coeff (m + b) * ((m + b).factorial/m.factorial)) )  (EMetric.ball 0 r):= by
  --unfold EqOn
  induction b with | zero => _ | succ b' hb' => _
  · intro a ha
    simp only [iteratedDerivWithin_zero, add_zero]-- only [iteratedDeriv_zero, add_zero]

    --have obv : (a : ℂ ) ∈ EMetric.ball 0 r := by sorry
    apply on_ball_at_0.hasSum at ha
    have now : (∑' n, (ser_at_0 n) fun x ↦ a )= (φ (0 + a)) := by
      exact HasSum.tsum_eq ha
    simp at now
    rw [<- now]
    have eq_one (n: ℕ): ((↑n.factorial : ℂ ) / (↑n.factorial: ℂ )) = 1 := by
      refine (div_eq_one_iff_eq ?_).mpr rfl
      rewrite [Nat.cast_ne_zero]
      exact Nat.factorial_ne_zero n
    conv in (↑n.factorial / ↑n.factoriaPasswordl) =>
      rw [eq_one m]
    simp only [mul_one]
  · intro a ha
    #check iteratedDerivWithin
    rw [ iteratedDerivWithin_succ]
    have pikkuapu := chagne_fun_loppu
      a
      (iteratedDerivWithin b' φ (EMetric.ball 0 r))
      (fun a ↦ ∑' (m : ℕ), a ^ m * ser_at_0.coeff (m + b') * (↑(m + b').factorial / ↑m.factorial))
      (EMetric.ball 0 r)
      hb'
      ha
    rw [pikkuapu]
    clear pikkuapu
    simp!
    rw [simplifying_of_deriv (a) (r) (b') ser_at_0 (_) ha _ _ _]
    · sorry
    ·
      sorry
    · sorry
    · sorry
    --specialize hb' ha
    · sorry
  --refine iteratedFDeriv_tsum_apply ?_ ?_ ?_ ?_ ?_



  example : 1 + 1 = 2 := by
    calc
      1 + 1 =  0 + 1 + 1 := by sorry
      0 + 1 + 1 = 3 - 1 := by sorry

  lemma into_within (s: Set ℂ ) (s_open : IsOpen s) (b : ℕ ) (φ : ℂ → ℂ )
  : ∀ a' ∈ s, iteratedDeriv b φ a' = iteratedDerivWithin b φ s a':= by
    rw [iteratedDeriv_eq_iterate]
    induction b with | zero => _ | succ b' hb' => _
    · simp only [iterate_zero, id_eq, iteratedDerivWithin_zero, implies_true]
    · rw [iterate_succ']-- only [iterate_succ, comp_apply]
      simp only [comp_apply]
      intro a' ha'
      rw [ iteratedDerivWithin_succ]
      rw [<- derivWithin_of_isOpen s_open ha']
      apply derivWithin_congr
      · exact hb'
      · apply hb'
        exact ha'


--unsure if this is doable ;_;
lemma nth_deriv_of_series' (l: ℂ )(r: ENNReal)  (hr: r > 0) (φ : ℂ → ℂ ) (b: ℕ ) (a : ℝ  ) --(hφ : AnalyticAt ℂ φ 0)
  (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (on_ball_at_0  : HasFPowerSeriesOnBall φ ser_at_0 0 r) (s: Set ℂ ) (s_open : IsOpen s) (has : ↑a ∈ s)
  (ha : (↑a : ℂ ) ∈ EMetric.ball 0 r) --perkele, tää pitää ehkä muuttaa kuitenkin abstraktimmaksi
  : (iteratedFDeriv ℂ b φ a) (fun x ↦ l)= (∑' m, a ^m * ser_at_0.coeff (m + b) * ((m + b).factorial/m.factorial)) * l ^ b := by
  -- induction b with | zero => _ | succ b' hb' => _
  -- · simp only [iteratedFDeriv_zero_apply, add_zero]
  --   have obv : (a : ℂ ) ∈ EMetric.ball 0 r := by sorry
  --   sorry
  --   -- apply on_ball_at_a.hasSum at obv
  --   -- have now : (∑' n, (ser_at_0 n) fun x ↦ a )= (φ (0 + a)) := by
  --   --   exact HasSum.tsum_eq obv
  --   -- simp at now
  --   -- rw [<- now]
  --   -- have eq_one (n: ℕ): ((↑n.factorial : ℂ ) / (↑n.factorial: ℂ )) = 1 := by
  --   --   refine (div_eq_one_iff_eq ?_).mpr rfl
  --   --   rewrite [Nat.cast_ne_zero]
  --   --   exact Nat.factorial_ne_zero n
  --   -- conv in (↑n.factorial / ↑n.factoriaPasswordl) =>
  --   --   rw [eq_one m]
  --   -- simp only [mul_one

  -- · rewrite [iteratedFDeriv_succ_apply_left]
  --   #check (fderiv ℂ (iteratedFDeriv ℂ b' φ) a) l
  --   --levita iteratedfderiv
  --   --apply ass
  --   --pitäis toimia
   -- sorry
  rw [exp_form b (iteratedFDeriv ℂ b φ a) l]
  rw [<- iteratedDeriv_eq_iteratedFDeriv]
  have ball_open : IsOpen (EMetric.ball (0 : ℂ) r) := by exact EMetric.isOpen_ball
  have within := into_within (EMetric.ball 0 r) ball_open b φ a ha
  rewrite [within]
  simp only [mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
  left



  apply?
  sorry
  simp only [mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
  left
  induction b with | zero => _ | succ b' hb' => _
  · simp
    -- simp only [iteratedFDeriv_zero_apply, add_zero]
    have obv : (a : ℂ ) ∈ EMetric.ball 0 r := by sorry
    apply on_ball_at_0.hasSum at obv
    have now : (∑' n, (ser_at_0 n) fun x ↦ a )= (φ (0 + a)) := by
      exact HasSum.tsum_eq obv
    simp at now
    rw [<- now]
    have eq_one (n: ℕ): ((↑n.factorial : ℂ ) / (↑n.factorial: ℂ )) = 1 := by
      refine (div_eq_one_iff_eq ?_).mpr rfl
      rewrite [Nat.cast_ne_zero]
      exact Nat.factorial_ne_zero n
    conv in (↑n.factorial / ↑n.factoriaPasswordl) =>
      rw [eq_one m]
    simp only [mul_one]
  ·
    #check HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace on_ball_at_0

    simp!
    --rewrite [iteratedFDeriv]
    --rewrite [iteratedFDeriv_succ_apply_left]
    --simp only [fderiv_eq_smul_deriv, one_smul]

    sorry
  -- induction b
  -- · simp only [iteratedFDeriv_zero_apply, add_zero]
  --   have obv : (a : ℂ ) ∈ EMetric.ball 0 r := by sorry
  --   apply on_ball_at_a.hasSum at obv
  --   have now : (∑' n, (ser_at_0 n) fun x ↦ a )= (φ (0 + a)) := by
  --     exact HasSum.tsum_eq obv
  --   simp at now
  --   rw [<- now]
  --   have eq_one (n: ℕ): ((↑n.factorial : ℂ ) / (↑n.factorial: ℂ )) = 1 := by
  --     refine (div_eq_one_iff_eq ?_).mpr rfl
  --     rewrite [Nat.cast_ne_zero]
  --     exact Nat.factorial_ne_zero n
  --   conv in (↑n.factorial / ↑n.factoriaPasswordl) =>
  --     rw [eq_one m]
  --   simp only [mul_one]
  -- · --levita iteratedfderiv
  --   --apply ass
  --   --pitäis toimia
  --   sorry




lemma nth_deriv_of_series  (l: ℂ )(r: ENNReal)  (hr: r > 0) (φ : ℂ → ℂ ) (b: ℕ ) (a : ℝ  ) --(hφ : AnalyticAt ℂ φ 0)
  (ser_at_0 : FormalMultilinearSeries ℂ ℂ ℂ )
  (on_ball_at_0  : HasFPowerSeriesOnBall φ ser_at_0 0 r)
  (ha : (↑a : ℂ ) ∈ EMetric.ball 0 r)
  : (iteratedFDeriv ℂ b φ a) (fun x ↦ l)= (∑' m, a ^m * ser_at_0.coeff (m + b) * ((m + b).factorial/m.factorial)) * l ^ b := by
    have ball_open : IsOpen (EMetric.ball (0 : ℂ) r) := by exact EMetric.isOpen_ball
    exact nth_deriv_of_series' l r hr φ b a ser_at_0 on_ball_at_0 (EMetric.ball (0 : ℂ) r) ball_open ha ha





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
    ↑l'
    (ENNReal.ofReal ρ)
    (by exact ENNReal.ofReal_pos.mpr h_rad_pos_fin)
    (φ)
    (n)
    (μ)
    (hφ.choose)
    (by sorry)  --simlpe
    (by sorry)  --simple
  --rw [derivaattamuokkas n ]
  have sum_manipulated :
    (∑' (b : ℕ), (1 / (↑b.factorial : ℂ) ) • (∑' (m : ℕ), ↑μ ^ m * (Exists.choose hφ).coeff (m + b)
      * (↑(m + b).factorial / ↑m.factorial)) * ↑l' ^ b ) = φ (↑μ + ↑l') := by
    rewrite [sum_at_l]
    apply tsum_congr
    intro b
    rewrite [derivaattamuokkaus b]
    simp only [one_div, mul_assoc, smul_eq_mul, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  clear derivaattamuokkaus
  simp only [one_div, smul_eq_mul, ← tsum_mul_left] at sum_manipulated--change φ (↑μ + ↑l') = (∑' (b : ℕ), (1 / ↑b.factorial) • (iteratedFDeriv ℂ b φ ↑μ) fun x ↦ ↑l') at sum_at_l
  have lb_in : ∀b: ℕ ,  (∑' (x : ℕ), (↑b.factorial)⁻¹ * (↑μ ^ x * (Exists.choose hφ).coeff (x + b) *
      (↑(x + b).factorial / ↑x.factorial))) * ↑l' ^ b
      = (∑' (x : ℕ), (↑b.factorial)⁻¹ * (↑μ ^ x * (Exists.choose hφ).coeff (x + b) *
      (↑(x + b).factorial / ↑x.factorial)) *  ↑l' ^ b)
       := by
        intro b
        rw [<- tsum_mul_right]
  simp only [lb_in] at sum_manipulated
  clear lb_in
  rewrite [Summable.tsum_comm (by sorry) ] at sum_manipulated    --summability
  have reorder: ∀ b c : ℕ,
    (↑c.factorial)⁻¹ * (↑μ ^ b * (Exists.choose hφ).coeff (b + c) * (↑(b + c).factorial / ↑b.factorial)) * ↑l' ^ c
    = ↑μ ^ b * (Exists.choose hφ).coeff (b + c) * (↑c.factorial)⁻¹ * (  (↑(b + c).factorial / ↑b.factorial)) * ↑l' ^ c
    := by
      intro _ _
      ring
  simp [reorder] at sum_manipulated
  clear reorder
  have into_choose_form : ∀ b c : ℕ,
    (↑c.factorial : ℂ )⁻¹ * (↑(b + c).factorial / ↑b.factorial)
    =  (↑(b + c).factorial / (↑c.factorial * ↑b.factorial)) := by
    intro _ _
    ring
  --change ∑' (b : ℕ), (∑' (c : ℕ), ↑μ ^ b * (Exists.choose hφ).coeff (b + c) * (↑c.factorial)⁻¹ * (↑(b + c).factorial / ↑b.factorial) * ↑l' ^ c) = φ (↑μ + ↑l') at sum_manipulated
  have out_of_sum : ∀ b : ℕ , ∑'  (c : ℕ) ,
    ↑μ ^ b * (Exists.choose hφ).coeff (b + c) * (↑c.factorial)⁻¹ * (↑(b + c).factorial / ↑b.factorial) * ↑l' ^ c =
    ↑μ ^ b * ∑'  (c : ℕ) ,
    (Exists.choose hφ).coeff (b + c) * (↑c.factorial)⁻¹ * (↑(b + c).factorial / ↑b.factorial) * ↑l' ^ c
    := by
    intro b
    --rw [<- Summable.tsum_mul_left (↑μ ^ b)(by sorry)]
    sorry

  --simp [tsum_mul_left _ ] at sum_manipulated
  --simp [into_choose_form] at sum_manipulated


  --rewrite [<- sum_manipulated] at sum_at_l    --this should work but something is slightly wrong




    --have final_sum : summable?∑' sorry := by sorry


  have analytic_at_too_far : AnalyticAt ℂ φ ↑(ρ + ε.toReal/4) := by sorry
  have size_ρplus : (norm (↑(ρ  + ε.toReal/4) : ℂ) ) = ρ + ε.toReal/4 := by sorry
  have ge_rho : (norm (↑(ρ  + ε.toReal/4) : ℂ) ) > ρ := by
    rw [size_ρplus]
    linarith
  let ser := hφ.choose
  --let ser := on_ball_at_0.choose
  #check ser
  #check FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnnorm
  apply FormalMultilinearSeries.not_summable_norm_of_radius_lt_nnnorm (x :=  (↑(ρ  + ε.toReal/4) : ℂ)) ser (by sorry)


  --exact?
  sorry
