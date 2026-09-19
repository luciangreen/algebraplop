:- begin_tests(complex_detlog_plop).

:- use_module('../complex_detlog_plop').

test(discover_affine_formula) :-
    Samples = [sample([i-1],3), sample([i-2],5), sample([i-3],7), sample([i-4],9)],
    discover_position_formula(Samples, Formula),
    eval_formula(Formula, [i-5], 11).

test(discover_length_dependent_formula) :-
    Samples = [sample([i-1,n-5],5), sample([i-2,n-5],4), sample([i-1,n-7],7), sample([i-3,n-7],5)],
    discover_position_formula(Samples, Formula),
    eval_formula(Formula, [i-2,n-8], 7).

test(discover_multivariable_formula) :-
    Samples = [sample([i-1,j-1],4), sample([i-2,j-1],6), sample([i-1,j-2],7), sample([i-3,j-2],11)],
    discover_position_formula(Samples, Formula),
    eval_formula(Formula, [i-4,j-3], 16).

test(discover_quadratic_formula) :-
    Samples = [sample([i-1],4), sample([i-2],9), sample([i-3],16), sample([i-4],25)],
    discover_position_formula(Samples, Formula),
    eval_formula(Formula, [i-5], 36).

test(discover_piecewise_formula) :-
    Samples = [sample([i-1],1), sample([i-2],2), sample([i-3],3), sample([i-4],6), sample([i-5],7)],
    discover_piecewise_formula(Samples, Formula),
    assertion(Formula == piecewise([when(leq(i,3),i), when(gt(i,3),i+2)])).

test(discover_recursive_formula) :-
    Trace = [0-1, 1-3, 2-5, 3-7],
    discover_recursive_formula(Trace, recursive(base(1), step(add(2)), closed_form(Formula))),
    eval_formula(Formula, [n-4], 9).

test(discover_address_formula) :-
    Samples = [sample([i-1,j-2],addr([2,1])), sample([i-3,j-4],addr([4,3])), sample([i-5,j-1],addr([1,5]))],
    discover_address_formula(Samples, Formula),
    assertion(Formula == addr([j,i])).

test(invert_affine_formula) :-
    invert_position_formula(2*i+1, Inverse, Guards),
    assertion(Inverse == (o-1)/2),
    assertion(Guards == [nonzero(2), divisible(o-1,2)]).

test(gaussian_inconsistent, [fail]) :-
    gaussian_solve([[1,1,3],[2,2,7]], _).

test(gaussian_underdetermined, [fail]) :-
    gaussian_solve([[1,1,3]], _).

test(false_correlation_rejected) :-
    Samples = [sample([i-1],1), sample([i-2],4), sample([i-3],9)],
    Program = position_program(square_like, Samples, [original_cost(plan(quadratic, 10))]),
    discover_position_algorithm(square_like, Program, Algorithm),
    assertion(Algorithm = position_algorithm(square_like, i, i^2, _, _, quadratic, experimental, keep_original, domain_not_proven, _, _)).

test(cost_model_rejection) :-
    Samples = [sample([i-1],3), sample([i-2],5), sample([i-3],7), sample([i-4],9)],
    Program = position_program(transform, Samples, [original_cost(plan(constant, 1)), verify_samples([sample([i-5],11)])]),
    discover_position_algorithm(transform, Program, Algorithm),
    assertion(Algorithm = position_algorithm(transform, i, Formula, _, _, affine, proven, keep_original, original_plan_cheaper, _, _)),
    eval_formula(Formula, [i-5], 11).

test(splice_index_loop_selected) :-
    Samples = [sample([i-1],3), sample([i-2],5), sample([i-3],7), sample([i-4],9)],
    Program = splice_ir(transform, Samples, [verify_samples([sample([i-5],11)]), original_cost(plan(quadratic, 20))]),
    splice_index_optimise(Program, Optimised, Report),
    assertion(Optimised = optimised_ir(transform, detlog(output_driven, deterministic), splice_index_loop(i, 1+2*i, (o-1)/2, [nonzero(2), divisible(o-1,2)]))),
    assertion(Report == selected(splice_index_loop, proven_equivalent_and_lower_cost)).

test(side_effect_rejection) :-
    Samples = [sample([i-1],3), sample([i-2],5), sample([i-3],7), sample([i-4],9)],
    Program = splice_ir(transform, Samples, [verify_samples([sample([i-5],11)]), side_effects(true)]),
    splice_index_optimise(Program, Optimised, Report),
    assertion(Optimised = splice_ir(transform, Samples, [verify_samples([sample([i-5],11)]), side_effects(true)])),
    assertion(Report == rejected(splice_index_loop, side_effect_dependency)).

test(program_to_r_spec) :-
    program_to_r_spec(
        optimised_ir(transform, detlog(output_driven, deterministic), splice_index_loop(i, 1+2*i, (o-1)/2, [nonzero(2), divisible(o-1,2)])),
        RSpec
    ),
    assertion(RSpec == r_spec(transform, [r(input_position(i), output_position(1+2*i), same_value, guards([nonzero(2), divisible(o-1,2)])), r(output_position(o), input_position((o-1)/2), same_value, guards([nonzero(2), divisible(o-1,2)]))])).

test(complex_optimise_program) :-
    Samples = [sample([i-1],3), sample([i-2],5), sample([i-3],7), sample([i-4],9)],
    Program = position_program(transform, Samples, [verify_samples([sample([i-5],11)]), original_cost(plan(quadratic, 20))]),
    complex_optimise_program(Program, Optimised, RSpec, Report),
    assertion(Optimised = optimised_ir(transform, detlog(output_driven, deterministic), splice_index_loop(i, 1+2*i, (o-1)/2, [nonzero(2), divisible(o-1,2)]))),
    assertion(RSpec = r_spec(transform, _)),
    assertion(Report = optimisation_report(transform, _, discovered(1+2*i, affine), verification(proven), _, _, decision(select_formula, proven_equivalent_and_lower_cost), _, _)).

:- end_tests(complex_detlog_plop).
