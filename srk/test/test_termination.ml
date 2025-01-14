open Srk
open Syntax
open OUnit
open Test_pervasives
open BatPervasives

module TF = TransitionFormula

let tr_symbols = [(wsym,wsym');(xsym,xsym');(ysym,ysym');(zsym,zsym')]

let has_llrf tf =
  TerminationLLRF.has_llrf (Iteration.Solver.make srk tf)

let mp_exp =
  let all_sym = (List.map fst tr_symbols)@(List.map snd tr_symbols) in
  fun tr_symbols phi ->
  TerminationExp.mp
    Iteration.LossyTranslation.exp
    (Iteration.Solver.make
       srk
       (TransitionFormula.make
          ~exists:(fun sym -> List.mem sym all_sym)
          phi
          tr_symbols))

let build_tf phi =
  let all_sym = (List.map fst tr_symbols)@(List.map snd tr_symbols) in
  TransitionFormula.make
    ~exists:(fun sym -> List.mem sym all_sym)
    phi
    tr_symbols

let mk_qqx vec =
  List.fold_left
    (fun vec (i, k) -> Polynomial.QQX.add_term k i vec)
    Polynomial.QQX.zero
    (List.mapi (fun i k -> (i, QQ.of_int k)) vec)

let mp_llrf_with_phase phi =
  let mp_llrf solver =
    if TerminationLLRF.has_llrf solver then
      Syntax.mk_false srk
    else
      let fresh_skolem =
        Memo.memo (fun sym -> mk_const srk (dup_symbol srk sym))
      in
      let subst sym =
        match (List.mem sym [xsym;xsym';ysym;ysym']) with
        | true -> mk_const srk sym
        | false -> fresh_skolem sym
      in
      substitute_const srk subst (Iteration.Solver.get_formula solver)
  in
  let predicates =
    List.map (fun (x,x') ->
        let x = mk_const srk x in
        let x' = mk_const srk x' in
        [mk_lt srk x x';
         mk_lt srk x' x;
         mk_eq srk x x'])
      (TF.symbols phi)
    |> List.concat
  in
  let star solver =
    let rtc =
      Iteration.closure
        Iteration.LossyTranslation.exp
        solver
    in
    let k = mk_symbol srk `TyInt in
    let tf = Iteration.Solver.get_transition_formula solver in
    let exists x = x != k && (TF.exists tf) x in
    TF.make
      ~exists
      rtc
      (TF.symbols tf)
  in
  let solver = Iteration.Solver.make srk phi in
  mk_not srk (Iteration.phase_mp srk predicates star mp_llrf solver)

let assert_equal_pz x y =
  assert_equal 
    ~cmp:Sequence.Periodic.equal 
    ~printer:(SrkUtil.mk_show (Sequence.Periodic.pp Format.pp_print_int)) x y

let assert_equal_pq x y =
  assert_equal 
    ~cmp:Sequence.Periodic.equal 
    ~printer:(SrkUtil.mk_show (Sequence.Periodic.pp QQ.pp)) x y

let mp_dta tf = TerminationDTA.mp (Iteration.Solver.make srk tf)

let suite = "Termination" >::: [
      "even" >:: (fun () ->
        let tr =
          Infix.(!(x = (int 0)) && x' = x - (int 2))
        in
        assert_equiv_quantified_formula
          Infix.((x mod (int 2)) = (int 0) && (int 0) <= x)
          (mp_exp tr_symbols tr)
      );
      "disjunctive_guard" >:: (fun () ->
        let tr =
          Infix.(((int 0) < x || (int 0) < y)
                 && (x' = x - (int 1) && y' = y - (int 1)))
        in
        assert_equiv_quantified_formula
          (mk_true srk)
          (mp_exp tr_symbols tr)
      );
      "midpoint" >:: (fun () ->
        let tr =
          Infix.((!(x = y)
                  && ((x' = x + (int 1) && y' = y)
                      || (x' = x && y' = y - (int 1)))))
        in
        assert_equiv_quantified_formula
          Infix.(x <= y)
          (mp_exp tr_symbols tr)
      );
      "llrf_1D" >:: (fun () ->
        let phi =
          Infix.( ((int 0) < x) && x' = x - (int 1))
          |> build_tf
        in
        assert_bool "Has LLRF" (has_llrf phi)
      );
      "llrf_2D" >:: (fun () ->
        let phi =
          Infix.( (int 0) < x &&
                    ( ((int 0) < y && (y' = y - (int 1)) && x' = x)
                      || (y <= (int 0)) && y' = (int 10) && x' = x - (int 1)))
          |> build_tf
        in
        assert_bool "Has LLRF" (has_llrf phi)
      );
      "llrf_sym_const" >:: (fun () ->
        let phi =
          TransitionFormula.make
            Infix.( (int 0) < x &&
                      ( (z < y && (y' = y - x) && x' = x)
                        || (y <= z) && x' = x - (int 1)))
            [(xsym,xsym');(ysym,ysym')]
        in
        assert_bool "Has LLRF" (has_llrf phi)
      );
      "no_llrf" >:: (fun () ->
        let phi =
          Infix.( (int 0) <= x &&
                    (((y' = y - (int 1)) && x' = x)
                     || x' = x - (int 1)))
          |> build_tf
        in
        assert_bool "No LLRF" (not (has_llrf phi))
      );
      "no_llrf_sym_const" >:: (fun () ->
        let phi =
          TransitionFormula.make
            ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym'])
            Infix.( (int 0) < x &&
                      ( (z < y && (y' = y - x) && x' = x)
                        || (y <= z) && x' = x - (int 1)))
            [(xsym,xsym');(ysym,ysym')]
        in
        assert_bool "No LLRF" (not (has_llrf phi))
      );
      "llrf_with_phase_1" >:: (fun () ->
        let phi =
          TransitionFormula.make
          ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym'])
          Infix.( (int 0) < x && x' = x - y && y' = y)
          [(xsym,xsym');(ysym,ysym')]
        in
        let expected_cond = Infix.((int 0) < y) in
        assert_bool "No LLRF" (not (has_llrf phi));
        assert_implies expected_cond (mp_llrf_with_phase phi)
      );
      "llrf_with_phase_2" >:: (fun () ->
        let phi =
          TransitionFormula.make
          ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym'])
          Infix.( (int 0) < x &&
                    ( ((int 0) <= y && (y' = y + (int 1)) && x' = x - (int 1))
                      || (y < (int 0)) && y' = y - (int 1) && x' = x + (int 1)))
          [(xsym,xsym');(ysym,ysym')]
        in
        let expected_cond = Infix.((int 0) <= y) in
        assert_bool "No LLRF" (not (has_llrf phi));
        assert_implies expected_cond (mp_llrf_with_phase phi)
      );
      "llrf_with_phase_3" >:: (fun () ->
        let phi =
          TransitionFormula.make
          ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym'])
          Infix.( (int 0) < x && (y' = y - (int 1)) && x' = x + y)
          [(xsym,xsym');(ysym,ysym')]
        in
        let expected_cond = mk_true srk in
        assert_bool "No LLRF" (not (has_llrf phi));
        assert_implies expected_cond (mp_llrf_with_phase phi)
      );
      "char_seq_of_qq_poly_mod1" >:: (fun () ->
        let p = (* 1/3x *)
          Polynomial.QQX.of_list [(QQ.of_frac 1 3, 1)]
        in
        assert_equal_pq
          (TerminationDTA.XSeq.seq_of_polynomial 2 p) 
          (Sequence.Periodic.make
             (List.map (fun i -> QQ.of_frac i 3) (BatList.of_enum (0 -- 5))))
      );
      "char_seq_of_poly_mod" >:: (fun () ->
        let p = mk_qqx [1; 2; 1] in
        (* n^2 + 2n + 1 mod 5 *)
        assert_equal_pq
          (TerminationDTA.XSeq.seq_of_polynomial 5 p) 
          (Sequence.Periodic.make (List.map QQ.of_int [1; 4; 4; 1; 0]))
      );
      "char_seq_of_exp_poly" >:: (fun () ->
        let p = ExpPolynomial.of_exponential (QQ.of_int 2) in 
        let q = ExpPolynomial.of_polynomial (mk_qqx [1; 1]) in
        let ep1 = ExpPolynomial.mul p q in
        let r = ExpPolynomial.of_exponential (QQ.of_int 3) in 
        let s = ExpPolynomial.of_polynomial (mk_qqx [0; 0; 1]) in
        let ep2 = ExpPolynomial.mul r s in
        let ep = ExpPolynomial.add ep1 ep2 in
        (* 2^n (n + 1) + 3^n (n^2) mod 5 *)
        assert_equal_pq
          (TerminationDTA.XSeq.seq_of_exp_polynomial 5 ep) 
          (Sequence.Periodic.make
             (List.map
                (fun i -> QQ.modulo (ExpPolynomial.eval ep i) (QQ.of_int 5))
                (BatList.of_enum (0 -- 19))))
      );
      "dta_omega_dom" >:: (fun () ->
        let tf =
          TransitionFormula.make
          ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym'])
          Infix.( x mod int 2 = int 0 && int 2 * x' = x)
          [(xsym,xsym')]
        in
        let expected_cond = mk_not srk (mk_eq srk x (mk_zero srk)) in
        assert_equiv_formula expected_cond (mp_dta tf)
      );
      "dta_cmp_0_atom_negative_coeff" >:: (fun () ->
        let tf =
          TransitionFormula.make
          ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym'])
          Infix.( (int 0) < x && y' = y - (int 1) && x' = x + y)
          [(xsym,xsym');(ysym,ysym')]
        in
        let expected_cond = mk_true srk in
        assert_equiv_formula expected_cond (mp_dta tf)
      );
      "dta_cmp_0_atom_poly" >:: (fun () ->
        let tf =
          TransitionFormula.make
          ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym'])
          Infix.( (int 0) <= x && y' = y && x' = x + y)
          [(xsym,xsym');(ysym,ysym')]
        in
        let expected_cond = mk_or srk 
          [ mk_and srk [mk_lt srk x (mk_zero srk); mk_leq srk y (mk_zero srk)]; 
            mk_lt srk y (mk_zero srk)] in
        assert_equiv_formula expected_cond (mp_dta tf)
      );
      "dta_divisibility_atom" >:: (fun () ->
        let tf =
          TransitionFormula.make
          ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym'])
          Infix.( x mod int 3 = int 0 && x' = x + y && y' = y)
          [(xsym,xsym');(ysym,ysym')]
        in
        (* not (x mod 3 = 0 /\ (x + y) mod 3 = 0 /\ (x + 2y) mod 3 = 0) *)
        let expected_cond = mk_not srk 
        (mk_and srk 
          [mk_eq srk (mk_mod srk x (mk_int srk 3)) (mk_zero srk);
          mk_eq srk (mk_mod srk (mk_add srk [x; y]) (mk_int srk 3)) (mk_zero srk);
          mk_eq srk 
            (mk_mod srk (mk_add srk [x; mk_mul srk [(mk_int srk 2); y]]) (mk_int srk 3)) 
            (mk_zero srk);
          ]) in
        assert_equiv_formula expected_cond (mp_dta tf)
      );
      "dta_conjunction" >:: (fun () ->
        let tf =
          TransitionFormula.make
          ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym';zsym;zsym'])
          Infix.( ( x mod int 3 = int 0 && int 0 <= y) && y' = y - z && x' = x + int 2 && z' = z)
          [(xsym,xsym');(ysym,ysym');(zsym, zsym')]
        in
        let expected_cond = mk_true srk in
        assert_equiv_formula expected_cond (mp_dta tf)
      );
      "dta_disjunction" >:: (fun () ->
        let tf =
          TransitionFormula.make
          ~exists:(fun w -> List.mem w [xsym;xsym';ysym;ysym';zsym;zsym'])
          Infix.( ((int 0) <= x || int 0 <= y) && y' = y - z && x' = x - z && z' = z)
          [(xsym,xsym');(ysym,ysym');(zsym, zsym')]
        in
        let expected_cond =
          Infix.((int 0) < z
                 || ((int 0) = z && x < (int 0) && y < (int 0)))
        in
        assert_equiv_formula expected_cond (mp_dta tf)
      );
    ]
