:- module(complex_detlog_plop,
    [ complex_optimise_file/2,
      complex_optimise_program/4,
      discover_position_algorithm/3,
      splice_index_optimise/3,
      program_to_r_spec/2,
      discover_position_formula/2,
      discover_recursive_formula/2,
      discover_address_formula/2,
      discover_piecewise_formula/2,
      invert_position_formula/3,
      gaussian_solve/2,
      compare_cost/3,
      eval_formula/3
    ]).

:- use_module(library(apply)).
:- use_module(library(lists)).
:- use_module(library(readutil)).

:- initialization(set_prolog_flag(prefer_rationals, true)).

complex_optimise_file(InputFile, OutputFile) :-
    setup_call_cleanup(
        open(InputFile, read, In),
        read_term(In, Program, []),
        close(In)
    ),
    complex_optimise_program(Program, OptimisedProgram, RSpec, Report),
    write_term_file(OutputFile, OptimisedProgram),
    auxiliary_output_paths(OutputFile, RSpecFile, ReportFile),
    write_term_file(RSpecFile, RSpec),
    write_term_file(ReportFile, Report).

complex_optimise_program(Program, OptimisedProgram, RSpec, Report) :-
    normalise_program(Program, Predicate, Samples, Options),
    discover_position_algorithm(Predicate, position_program(Predicate, Samples, Options), Algorithm),
    splice_index_optimise(splice_ir(Predicate, Samples, Options), OptimisedProgram, SpliceReport),
    program_to_r_spec(OptimisedProgram, RSpec),
    Algorithm = position_algorithm(_, _, Formula, _, _, Method, Safety, Decision, Reason, OriginalCost, FormulaCost),
    Report = optimisation_report(
        Predicate,
        [deterministic, splice, positional_provenance, formula_discovery],
        discovered(Formula, Method),
        verification(Safety),
        original_cost(OriginalCost),
        optimised_cost(FormulaCost),
        decision(Decision, Reason),
        splice_report(SpliceReport),
        final_positional_spec(RSpec)
    ).

splice_index_optimise(splice_ir(Predicate, Samples, Options), OptimisedIR, Report) :-
    discover_position_algorithm(Predicate, position_program(Predicate, Samples, Options), Algorithm),
    Algorithm = position_algorithm(_, InputVar, Formula, Inverse, Guards, _, Safety, Decision, Reason, _, _),
    ( safety_safe(Safety),
      Decision == select_formula
    -> OptimisedIR = optimised_ir(
           Predicate,
           detlog(output_driven, deterministic),
           splice_index_loop(InputVar, Formula, Inverse, Guards)
       ),
       Report = selected(splice_index_loop, Reason)
    ; OptimisedIR = splice_ir(Predicate, Samples, Options),
      Report = rejected(splice_index_loop, Reason)
    ).

program_to_r_spec(optimised_ir(Predicate, _, splice_index_loop(InputVar, Formula, Inverse, Guards)), RSpec) :-
    formula_r_terms(InputVar, Formula, Guards, MainTerms),
    inverse_r_terms(Inverse, Guards, InverseTerms),
    append(MainTerms, InverseTerms, Terms),
    RSpec = r_spec(Predicate, Terms).
program_to_r_spec(splice_ir(Predicate, _, _), r_spec(Predicate, [])).

discover_position_algorithm(Predicate, Program, Algorithm) :-
    normalise_program(Program, _, Samples, Options),
    position_input_variable(Samples, InputVar),
    ( outputs_are_addresses(Samples) ->
        discover_address_formula(Samples, Formula),
        Method = address,
        basis_size(Formula, BasisSize)
    ; discover_position_formula_internal(Samples, Formula, Method, BasisSize)
    ),
    option_value(Options, verify_samples, [], VerifySamples),
    append(Samples, VerifySamples, AllSamples),
    verify_formula(AllSamples, Formula),
    ( invert_position_formula(Formula, Inverse, Guards) -> true ; Inverse = none, Guards = [] ),
    option_value(Options, original_cost, plan(quadratic, 100), OriginalCost),
    estimate_formula_cost(Formula, FormulaCost),
    compare_cost(OriginalCost, FormulaCost, CostDecision),
    classify_safety(Options, Samples, VerifySamples, BasisSize, Safety),
    decide_selection(Options, Safety, CostDecision, Reason, Decision),
    Algorithm = position_algorithm(
        Predicate,
        InputVar,
        Formula,
        Inverse,
        Guards,
        Method,
        Safety,
        Decision,
        Reason,
        OriginalCost,
        FormulaCost
    ).
discover_position_algorithm(Predicate, Program, position_algorithm(Predicate, i, none, none, [], none, experimental, keep_original, insufficient_samples, plan(quadratic, 100), plan(linear, 1))) :-
    normalise_program(Program, _, Samples, _),
    Samples \= [],
    \+ outputs_are_addresses(Samples),
    \+ discover_position_formula_internal(Samples, _, _, _).

discover_position_formula(Samples, Formula) :-
    discover_position_formula_internal(Samples, Formula, _, _).

discover_position_formula_internal(Samples, Formula, identity, 1) :-
    position_input_variable(Samples, Var),
    Formula = Var,
    forall(member(Sample, Samples), (sample_output(Sample, Output), sample_lookup(Sample, Var, Output))).
discover_position_formula_internal(Samples, Formula, constant, 1) :-
    Samples = [First|_],
    sample_output(First, Formula),
    forall(member(Sample, Samples), sample_output(Sample, Formula)).
discover_position_formula_internal(Samples, Formula, offset, 2) :-
    position_input_variable(Samples, Var),
    Samples = [First|_],
    sample_lookup(First, Var, I0),
    sample_output(First, O0),
    Offset is O0 - I0,
    Formula0 = Var+Offset,
    simplify_formula(Formula0, Formula),
    verify_formula(Samples, Formula).
discover_position_formula_internal(Samples, Formula, scale, 1) :-
    position_input_variable(Samples, Var),
    scale_factor(Samples, Var, Scale),
    Formula0 = Scale*Var,
    simplify_formula(Formula0, Formula),
    verify_formula(Samples, Formula).
discover_position_formula_internal(Samples, Formula, affine, 2) :-
    position_input_variable(Samples, Var),
    solve_for_basis(Samples, [1, Var], Formula),
    verify_formula(Samples, Formula).
discover_position_formula_internal(Samples, Formula, length_affine, 3) :-
    position_input_variable(Samples, Var),
    samples_have_variable(Samples, n),
    solve_for_basis(Samples, [1, Var, n], Formula),
    verify_formula(Samples, Formula).
discover_position_formula_internal(Samples, Formula, two_var_affine, 3) :-
    position_input_variable(Samples, Var),
    secondary_input_variable(Samples, Var, Other),
    solve_for_basis(Samples, [1, Var, Other], Formula),
    verify_formula(Samples, Formula).
discover_position_formula_internal(Samples, Formula, multivariable_affine, 4) :-
    position_input_variable(Samples, Var),
    secondary_input_variable(Samples, Var, Other),
    samples_have_variable(Samples, n),
    solve_for_basis(Samples, [1, Var, Other, n], Formula),
    verify_formula(Samples, Formula).
discover_position_formula_internal(Samples, Formula, quadratic, 3) :-
    position_input_variable(Samples, Var),
    solve_for_basis(Samples, [1, Var, Var^2], Formula),
    verify_formula(Samples, Formula).
discover_position_formula_internal(Samples, Formula, recursive_closed_form, 2) :-
    discover_recursive_formula(Samples, recursive(_, _, closed_form(Formula))).
discover_position_formula_internal(Samples, Formula, piecewise, 4) :-
    discover_piecewise_formula(Samples, Formula).

discover_recursive_formula(Trace, recursive(base(Base), step(add(Step)), closed_form(Formula))) :-
    normalise_trace(Trace, Pairs),
    Pairs = [0-Base, 1-Next|_],
    Step is Next - Base,
    forall(consecutive_pair(Pairs, N1-O1, N2-O2), (N2 =:= N1 + 1, O2 - O1 =:= Step)),
    Formula0 = Step*n + Base,
    simplify_formula(Formula0, Formula).

discover_address_formula(Samples, addr(Formulas)) :-
    Samples = [First|_],
    sample_output(First, addr(FirstAddress)),
    length(FirstAddress, Arity),
    numlist(1, Arity, Indexes),
    maplist(address_coordinate_formula(Samples), Indexes, Formulas).

discover_piecewise_formula(Samples, BestFormula) :-
    position_input_variable(Samples, Var),
    findall(Value, (member(Sample, Samples), sample_lookup(Sample, Var, Value)), RawValues),
    sort(RawValues, Values),
    findall(Score-piecewise([when(leq(Var, Split), LeftFormula), when(gt(Var, Split), RightFormula)]),
        ( adjacent_split(Values, Split),
          partition_samples(Var, Split, Samples, LeftSamples, RightSamples),
          LeftSamples \= [],
          RightSamples \= [],
          discover_non_piecewise_formula(LeftSamples, LeftFormula),
          discover_non_piecewise_formula(RightSamples, RightFormula),
          LeftFormula \= RightFormula,
          verify_formula(Samples, piecewise([when(leq(Var, Split), LeftFormula), when(gt(Var, Split), RightFormula)])),
          expr_size(LeftFormula, LeftSize),
          expr_size(RightFormula, RightSize),
          Score is LeftSize + RightSize
        ),
        Candidates),
    keysort(Candidates, [_-BestFormula|_]).

invert_position_formula(Formula, Inverse, Guards) :-
    affine_components(Formula, Var, A, B),
    A =\= 0,
    simplify_formula((o-B)/A, Inverse),
    ( abs(A) =:= 1 ->
        Guards = [nonzero(A)]
    ; Guards = [nonzero(A), divisible(o-B, A)]
    ),
    atom(Var).

gaussian_solve(Matrix, Solution) :-
    Matrix = [FirstRow|_],
    length(FirstRow, Width),
    Vars is Width - 1,
    length(Matrix, Vars),
    maplist(split_equation_row, Matrix, CoeffRows, Constants),
    determinant(CoeffRows, Determinant),
    Determinant =\= 0,
    numlist(1, Vars, Indexes),
    maplist(cramer_value(CoeffRows, Constants, Determinant), Indexes, Solution).

compare_cost(OriginalCost, FormulaCost, Decision) :-
    cost_rank(OriginalCost, OriginalRank, OriginalWork),
    cost_rank(FormulaCost, FormulaRank, FormulaWork),
    ( FormulaRank < OriginalRank -> Decision = select_formula
    ; FormulaRank > OriginalRank -> Decision = keep_original
    ; FormulaWork < OriginalWork -> Decision = select_formula
    ; FormulaWork > OriginalWork -> Decision = keep_original
    ; Decision = same_cost
    ).

normalise_program(position_program(Predicate, Samples, Options), Predicate, Samples, Options).
normalise_program(program(Predicate, Samples, Options), Predicate, Samples, Options).
normalise_program(position_program(Predicate, Samples), Predicate, Samples, []).
normalise_program(program(Predicate, Samples), Predicate, Samples, []).

write_term_file(Path, Term) :-
    setup_call_cleanup(
        open(Path, write, Out),
        ( write_term(Out, Term, [quoted(true), fullstop(true), nl(true)]) ),
        close(Out)
    ).

auxiliary_output_paths(OutputFile, RSpecFile, ReportFile) :-
    file_name_extension(Base, _, OutputFile),
    atom_concat(Base, '.r.pl', RSpecFile),
    atom_concat(Base, '.report.txt', ReportFile).

formula_r_terms(_InputVar, recursive(base(Base), step(add(Step)), closed_form(ClosedForm)), Guards,
    [ r(base, input_position(0), output_position(Base), guards([])),
      r(step, input_position(n), output_position(ClosedForm), guards([delta(Step)|Guards]))
    ]).
formula_r_terms(InputVar, piecewise(Branches), Guards, [r(input_position(InputVar), output_position(piecewise(Branches)), same_value, guards(Guards))]).
formula_r_terms(InputVar, Formula, Guards, [r(input_position(InputVar), output_position(Formula), same_value, guards(Guards))]).

inverse_r_terms(none, _, []).
inverse_r_terms(Inverse, Guards, [r(output_position(o), input_position(Inverse), same_value, guards(Guards))]).

classify_safety(Options, Samples, VerifySamples, BasisSize, unsafe) :-
    option_true(Options, side_effects),
    !,
    Samples \= [],
    VerifySamples = VerifySamples,
    BasisSize = BasisSize.
classify_safety(Options, _, _, _, exhaustively_verified) :-
    option_true(Options, exhaustive_domain),
    !.
classify_safety(_, _, VerifySamples, _, proven) :-
    VerifySamples \= [],
    !.
classify_safety(_, Samples, _, BasisSize, verified_domain(observed(Count))) :-
    length(Samples, Count),
    Count > BasisSize,
    !.
classify_safety(_, _, _, _, experimental).

decide_selection(Options, unsafe, _, side_effect_dependency, keep_original) :-
    option_true(Options, side_effects),
    !.
decide_selection(_, Safety, select_formula, proven_equivalent_and_lower_cost, select_formula) :-
    safety_safe(Safety),
    !.
decide_selection(_, Safety, same_cost, same_complexity_no_demonstrated_gain, keep_original) :-
    safety_safe(Safety),
    !.
decide_selection(_, experimental, _, domain_not_proven, keep_original) :-
    !.
decide_selection(_, _, keep_original, original_plan_cheaper, keep_original).

affine_components(Formula, Var, A, B) :-
    simplify_formula(Formula, Simplified),
    affine_components_(Simplified, Var, A, B).

affine_components_(Var, Var, 1, 0) :- atom(Var).
affine_components_(A*Var, Var, A, 0) :- number(A), atom(Var).
affine_components_(Var*A, Var, A, 0) :- number(A), atom(Var).
affine_components_(Var+B, Var, 1, B) :- atom(Var), number(B).
affine_components_(B+Var, Var, 1, B) :- atom(Var), number(B).
affine_components_(A*Var+B, Var, A, B) :- number(A), atom(Var), number(B).
affine_components_(B+A*Var, Var, A, B) :- number(A), atom(Var), number(B).
affine_components_(A*Var-B, Var, A, NegB) :- number(A), atom(Var), number(B), NegB is -B.

solve_for_basis(Samples, Basis, Formula) :-
    basis_rows(Samples, Basis, Rows),
    length(Basis, Count),
    combination(Count, Rows, CandidateRows),
    gaussian_solve(CandidateRows, Coeffs),
    build_linear_formula(Basis, Coeffs, Formula0),
    simplify_formula(Formula0, Formula),
    verify_formula(Samples, Formula),
    !.

basis_rows(Samples, Basis, Rows) :-
    maplist(sample_basis_row(Basis), Samples, Rows).

sample_basis_row(Basis, Sample, Row) :-
    sample_pairs(Sample, Vars),
    maplist(eval_formula_with_vars(Vars), Basis, BasisValues),
    sample_output(Sample, Output),
    append(BasisValues, [Output], Row).

build_linear_formula(Basis, Coeffs, Formula) :-
    maplist(weighted_basis_term, Coeffs, Basis, Terms0),
    exclude(==(0), Terms0, Terms),
    terms_sum(Terms, Formula).

weighted_basis_term(0, _, 0) :- !.
weighted_basis_term(Coeff, 1, Coeff) :- !.
weighted_basis_term(1, Basis, Basis) :- !.
weighted_basis_term(Coeff, Basis, Coeff*Basis).

terms_sum([], 0).
terms_sum([Term], Term) :- !.
terms_sum([Term|Terms], Sum) :-
    terms_sum(Terms, Tail),
    Sum = Term + Tail.

verify_formula(Samples, addr(Formulas)) :-
    maplist(verify_address_formula(Formulas), Samples).
verify_formula([], _).
verify_formula([Sample|Samples], Formula) :-
    sample_output(Sample, Expected),
    sample_pairs(Sample, Vars),
    eval_formula(Formula, Vars, Actual),
    Actual =:= Expected,
    verify_formula(Samples, Formula).

verify_address_formula(Formulas, Sample) :-
    sample_output(Sample, addr(Expected)),
    sample_pairs(Sample, Vars),
    maplist(eval_formula_with_vars(Vars), Formulas, Actual),
    Actual = Expected.

estimate_formula_cost(Formula, plan(linear, Work)) :-
    expr_size(Formula, Work0),
    Work is max(1, Work0).

expr_size(Number, 1) :- number(Number), !.
expr_size(Atom, 1) :- atom(Atom), !.
expr_size(addr(Formulas), Size) :-
    maplist(expr_size, Formulas, Sizes),
    sum_list(Sizes, Sum),
    Size is Sum + 1.
expr_size(piecewise(Branches), Size) :-
    findall(BranchSize,
        ( member(when(Cond, Expr), Branches),
          condition_size(Cond, CondSize),
          expr_size(Expr, ExprSize),
          BranchSize is CondSize + ExprSize + 1
        ),
        Sizes),
    sum_list(Sizes, Sum),
    Size is Sum + 1.
expr_size(recursive(_, _, closed_form(Formula)), Size) :-
    expr_size(Formula, Inner),
    Size is Inner + 1.
expr_size(Expr, Size) :-
    Expr =.. [_|Args],
    maplist(expr_size, Args, Sizes),
    sum_list(Sizes, Sum),
    Size is Sum + 1.

condition_size(Condition, Size) :-
    Condition =.. [_|Args],
    maplist(expr_size, Args, Sizes),
    sum_list(Sizes, Sum),
    Size is Sum + 1.

samples_have_variable(Samples, Var) :-
    member(Sample, Samples),
    sample_lookup(Sample, Var, _),
    !.

outputs_are_addresses([Sample|_]) :-
    sample_output(Sample, addr(_)).

position_input_variable(Samples, Var) :-
    sample_variables(Samples, Vars),
    ( member(i, Vars) -> Var = i ; Vars = [Var|_] ).

secondary_input_variable(Samples, Primary, Var) :-
    sample_variables(Samples, Vars),
    exclude(==(Primary), Vars, Others),
    exclude(==(n), Others, OthersWithoutN),
    ( OthersWithoutN = [Var|_] -> true ; Others = [Var|_] ).

sample_variables(Samples, Vars) :-
    findall(Var,
        ( member(Sample, Samples),
          sample_pairs(Sample, Pairs),
          member(Var-_, Pairs)
        ),
        RawVars),
    sort(RawVars, Vars).

sample_pairs(sample(Vars, _), Pairs) :- !, pairs_from(Vars, Pairs).
sample_pairs(sample(Vars, _, Context), Pairs) :- !,
    pairs_from(Vars, VarsPairs),
    pairs_from(Context, ContextPairs),
    append(VarsPairs, ContextPairs, Pairs).
sample_pairs(trace(Vars, _, Context), Pairs) :- !,
    pairs_from(Vars, VarsPairs),
    pairs_from(Context, ContextPairs),
    append(VarsPairs, ContextPairs, Pairs).

sample_output(sample(_, Output), Output).
sample_output(sample(_, Output, _), Output).
sample_output(trace(_, Output, _), Output).

sample_lookup(Sample, Key, Value) :-
    sample_pairs(Sample, Pairs),
    memberchk(Key-Value, Pairs).

pairs_from(Dict, Pairs) :- is_dict(Dict), !, dict_pairs(Dict, _, Pairs).
pairs_from(List, List).

option_value(Options, Key, Default, Value) :-
    Goal =.. [Key, Value],
    ( memberchk(Goal, Options) -> true ; Value = Default ).

option_true(Options, Key) :-
    Goal =.. [Key, true],
    memberchk(Goal, Options).

scale_factor(Samples, Var, Scale) :-
    include(non_zero_input(Var), Samples, NonZeroSamples),
    NonZeroSamples \= [],
    NonZeroSamples = [First|Rest],
    sample_lookup(First, Var, I0),
    sample_output(First, O0),
    Scale is O0 / I0,
    forall(member(Sample, Rest),
        ( sample_lookup(Sample, Var, I),
          sample_output(Sample, O),
          O =:= Scale*I
        )).

non_zero_input(Var, Sample) :-
    sample_lookup(Sample, Var, Value),
    Value =\= 0.

adjacent_split([Left, Right|_], Left) :- Left < Right.
adjacent_split([_|Rest], Split) :- adjacent_split(Rest, Split).

partition_samples(Var, Split, Samples, LeftSamples, RightSamples) :-
    include(sample_leq(Var, Split), Samples, LeftSamples),
    include(sample_gt(Var, Split), Samples, RightSamples).

sample_leq(Var, Split, Sample) :- sample_lookup(Sample, Var, Value), Value =< Split.
sample_gt(Var, Split, Sample) :- sample_lookup(Sample, Var, Value), Value > Split.

discover_non_piecewise_formula(Samples, Formula) :-
    discover_position_formula_internal(Samples, Formula, Method, _),
    Method \= piecewise.

address_coordinate_formula(Samples, Index, Formula) :-
    findall(sample(Vars, Value),
        ( member(sample(Vars, addr(Address)), Samples), nth1(Index, Address, Value) ),
        CoordinateSamples),
    discover_position_formula(CoordinateSamples, Formula).

normalise_trace(Trace, Pairs) :-
    maplist(trace_pair, Trace, Pairs),
    sort(Pairs, Pairs).

trace_pair(N-Value, N-Value) :- !.
trace_pair(sample(Vars, Value), N-Value) :- !, memberchk(n-N, Vars).
trace_pair(sample(Vars, Value, _), N-Value) :- memberchk(n-N, Vars).

consecutive_pair([A, B|_], A, B).
consecutive_pair([_|Rest], A, B) :- consecutive_pair(Rest, A, B).

basis_size(addr(Formulas), Size) :- length(Formulas, Size), !.
basis_size(piecewise(Branches), Size) :- length(Branches, BranchCount), Size is BranchCount * 2, !.
basis_size(recursive(_, _, closed_form(Formula)), Size) :- expr_size(Formula, Size), !.
basis_size(Formula, Size) :- expr_size(Formula, Size).

safety_safe(proven).
safety_safe(exhaustively_verified).
safety_safe(verified_domain(_)).

cost_rank(plan(Complexity, Work), Rank, Work) :- !, complexity_rank(Complexity, Rank).
cost_rank(Work, 0, Work) :- number(Work).

complexity_rank(constant, 0).
complexity_rank(linear, 1).
complexity_rank(nlogn, 2).
complexity_rank(quadratic, 3).
complexity_rank(cubic, 4).
complexity_rank(exponential, 5).

split_equation_row(Row, Coeffs, Constant) :-
    append(Coeffs, [Constant], Row).

cramer_value(CoeffRows, Constants, Determinant, Index, Value) :-
    replace_column(CoeffRows, Index, Constants, AdjustedRows),
    determinant(AdjustedRows, Numerator),
    Value is Numerator / Determinant.

replace_column([], _, [], []).
replace_column([Row|Rows], Index, [Constant|Constants], [AdjustedRow|AdjustedRows]) :-
    replace_nth1(Row, Index, Constant, AdjustedRow),
    replace_column(Rows, Index, Constants, AdjustedRows).

replace_nth1([_|Rest], 1, Value, [Value|Rest]) :- !.
replace_nth1([Item|Rest], Index, Value, [Item|Adjusted]) :-
    Index > 1,
    NextIndex is Index - 1,
    replace_nth1(Rest, NextIndex, Value, Adjusted).

determinant([[Value]], Value) :- !.
determinant(Matrix, Determinant) :-
    Matrix = [FirstRow|_],
    findall(Term,
        ( nth1(Index, FirstRow, Element),
          minor_matrix(Matrix, 1, Index, Minor),
          determinant(Minor, MinorDet),
          Sign is (-1)^(1+Index),
          Term is Sign*Element*MinorDet
        ),
        Terms),
    sum_list(Terms, Determinant).

minor_matrix(Matrix, RowIndex, ColumnIndex, Minor) :-
    nth1(RowIndex, Matrix, _, RemainingRows),
    maplist(remove_nth1(ColumnIndex), RemainingRows, Minor).

remove_nth1(Index, Row, Reduced) :-
    nth1(Index, Row, _, Reduced).

combination(0, _, []) :- !.
combination(N, [X|Xs], [X|Ys]) :-
    N > 0,
    N1 is N - 1,
    combination(N1, Xs, Ys).
combination(N, [_|Xs], Ys) :-
    N > 0,
    combination(N, Xs, Ys).

eval_formula_with_vars(Vars, Formula, Value) :-
    eval_formula(Formula, Vars, Value).

eval_formula(Expr, _, Expr) :- number(Expr), !.
eval_formula(Expr, Vars, Value) :- atom(Expr), !, memberchk(Expr-Value, Vars).
eval_formula(A+B, Vars, Value) :- !,
    eval_formula(A, Vars, Left),
    eval_formula(B, Vars, Right),
    Value is Left + Right.
eval_formula(A-B, Vars, Value) :- !,
    eval_formula(A, Vars, Left),
    eval_formula(B, Vars, Right),
    Value is Left - Right.
eval_formula(A*B, Vars, Value) :- !,
    eval_formula(A, Vars, Left),
    eval_formula(B, Vars, Right),
    Value is Left * Right.
eval_formula(A/B, Vars, Value) :- !,
    eval_formula(A, Vars, Left),
    eval_formula(B, Vars, Right),
    Right =\= 0,
    Value is Left / Right.
eval_formula(A^B, Vars, Value) :- !,
    eval_formula(A, Vars, Left),
    eval_formula(B, Vars, Right),
    Value is Left^Right.
eval_formula(piecewise(Branches), Vars, Value) :- !,
    member(when(Condition, Expr), Branches),
    eval_condition(Condition, Vars),
    eval_formula(Expr, Vars, Value),
    !.
eval_formula(recursive(_, _, closed_form(Formula)), Vars, Value) :- !,
    eval_formula(Formula, Vars, Value).
eval_formula(addr(Formulas), Vars, addr(Values)) :- !,
    maplist(eval_formula_with_vars(Vars), Formulas, Values).

eval_condition(leq(A, B), Vars) :- eval_formula(A, Vars, Left), eval_formula(B, Vars, Right), Left =< Right.
eval_condition(geq(A, B), Vars) :- eval_formula(A, Vars, Left), eval_formula(B, Vars, Right), Left >= Right.
eval_condition(lt(A, B), Vars) :- eval_formula(A, Vars, Left), eval_formula(B, Vars, Right), Left < Right.
eval_condition(gt(A, B), Vars) :- eval_formula(A, Vars, Left), eval_formula(B, Vars, Right), Left > Right.
eval_condition(eq(A, B), Vars) :- eval_formula(A, Vars, Left), eval_formula(B, Vars, Right), Left =:= Right.
eval_condition(mod_eq(A, Modulus, Expected), Vars) :-
    eval_formula(A, Vars, Value),
    eval_formula(Modulus, Vars, M),
    eval_formula(Expected, Vars, E),
    M =\= 0,
    Value mod M =:= E.

group_numbers([A, B], Value) :- Value is A + B.

simplify_formula(Expr, Simplified) :-
    ( number(Expr) ; atom(Expr) ),
    !,
    Simplified = Expr.
simplify_formula(addr(Formulas), addr(Simplified)) :- !,
    maplist(simplify_formula, Formulas, Simplified).
simplify_formula(piecewise(Branches), piecewise(SimplifiedBranches)) :- !,
    maplist(simplify_branch, Branches, SimplifiedBranches).
simplify_formula(recursive(Base, Step, closed_form(Formula)), recursive(Base, Step, closed_form(Simplified))) :- !,
    simplify_formula(Formula, Simplified).
simplify_formula(A+B, Simplified) :- !,
    simplify_formula(A, Left0),
    simplify_formula(B, Right0),
    simplify_add(Left0, Right0, Simplified).
simplify_formula(A-B, Simplified) :- !,
    simplify_formula(A, Left0),
    simplify_formula(B, Right0),
    simplify_subtract(Left0, Right0, Simplified).
simplify_formula(A*B, Simplified) :- !,
    simplify_formula(A, Left0),
    simplify_formula(B, Right0),
    simplify_multiply(Left0, Right0, Simplified).
simplify_formula(A/B, Simplified) :- !,
    simplify_formula(A, Left0),
    simplify_formula(B, Right0),
    simplify_divide(Left0, Right0, Simplified).
simplify_formula(A^B, Simplified) :- !,
    simplify_formula(A, Left0),
    simplify_formula(B, Right0),
    simplify_power(Left0, Right0, Simplified).

simplify_branch(when(Condition, Expr), when(Condition, SimplifiedExpr)) :-
    simplify_formula(Expr, SimplifiedExpr).

simplify_add(0, X, X) :- !.
simplify_add(X, 0, X) :- !.
simplify_add(X, X, Simplified) :- !, simplify_multiply(2, X, Simplified).
simplify_add(A, B, Simplified) :- number(A), number(B), !, Simplified is A + B.
simplify_add(A, B, A+B).

simplify_subtract(X, 0, X) :- !.
simplify_subtract(A, B, Simplified) :- number(A), number(B), !, Simplified is A - B.
simplify_subtract(A, B, A-B).

simplify_multiply(0, _, 0) :- !.
simplify_multiply(_, 0, 0) :- !.
simplify_multiply(1, X, X) :- !.
simplify_multiply(X, 1, X) :- !.
simplify_multiply(A, B, Simplified) :- number(A), number(B), !, Simplified is A * B.
simplify_multiply(A, B, A*B).

simplify_divide(X, 1, X) :- !.
simplify_divide(A, B, Simplified) :- number(A), number(B), B =\= 0, !, Simplified is A / B.
simplify_divide(A, B, A/B).

simplify_power(_, 0, 1) :- !.
simplify_power(X, 1, X) :- !.
simplify_power(A, B, Simplified) :- number(A), number(B), !, Simplified is A^B.
simplify_power(A, B, A^B).
