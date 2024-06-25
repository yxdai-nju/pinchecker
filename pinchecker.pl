% -*- coding: iso_8859_1 -*-
% 
% File: pinchecker.pl
% Description: Generate Rust code that violates the Pin contract
%
% Version: 0.1.0
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>

:- use_module(library(lists)).
:- use_module(library(plunit)).

fn_typing(unmovable_new_F, [], unmovable_T).
fn_typing(move_F, [T], T) .
fn_typing(borrow_F, [T], ref_T(T)).
fn_typing(borrow_mut_F, [T], mutref_T(T)).
fn_typing(option_some_F, [T], option_T(T)).
fn_typing(option_none_F, [], option_T(_)).

fn_rpil(unmovable_new_F,
        []).
fn_rpil(move_F,
        [rpil_kill(op(1))
        ,rpil_bind(op(0), op(1))
        ,rpil_move(op(1))
        ]).
fn_rpil(borrow_F,
        [rpil_borrow(op(0), op(1))
        ]).
fn_rpil(borrow_mut_F,
        [rpil_borrow_mut(op(0), op(1))
        ]).
fn_rpil(option_some_F,
        [rpil_kill(op(1))
        ,rpil_bind(place(op(0),1), op(1))
        ,rpil_move(op(1))
        ]).
fn_rpil(option_none_F,
        []).

impl_trait(ref_T(_), copy_Tr).
impl_trait(option_T(T), copy_Tr) :- impl_trait(T, copy_Tr).

lives_even_after_killing(mutref_T(_)) :- !.
lives_even_after_killing(T) :- impl_trait(T, copy_Tr).

% =============================================================================

fn_rpil_reduced(Func, Ops, RpilReduced) :-
        fn_rpil(Func, Rpil),
        rpil_reduction(Ops, Rpil, RpilReduced).

rpil_reduction(Ops, Rpil, RpilReduced) :-
        maplist(rpil_inst_reduction(Ops), Rpil, RpilReduced).

rpil_inst_reduction(Ops, Inst, InstReduced) :-
        Inst =.. [Name|Terms],
        maplist(rpil_term_reduction(Ops), Terms, TermsReduced),
        InstReduced =.. [Name|TermsReduced].

rpil_term_reduction(Ops, op(Idx), Var) :-
        !, nth0(Idx, Ops, Var).
rpil_term_reduction(Ops, place(Term, P), place(TermReduced, P)) :-
        rpil_term_reduction(Ops, Term, TermReduced), !.
rpil_term_reduction(Ops, deref(Term), deref(TermReduced)) :-
        rpil_term_reduction(Ops, Term, TermReduced), !.

ctx_typing(Stmts, Var, Type) :-
        length(Stmts, L), Stmts = [Stmt|StmtsR],
        Stmt = funcall(L, Func, Args),
        (   Var = L ->
            fn_typing(Func, ArgTypes, Type),
            maplist(alive_var_type(StmtsR), Args, ArgTypes)
        ;   ctx_typing(StmtsR, Var, Type)
        ).

alive_var_type(Stmts, Var, Type) :-
    ctx_liveness(Stmts, Var, alive),
    ctx_typing(Stmts, Var, Type).

ctx_liveness(Stmts, Var, Liveness) :-
        length(Stmts, L), Stmts = [Stmt|StmtsR],
        Stmt = funcall(L, Func, Args),
        ctx_typing(Stmts, L, _),
        (   Var = L ->
            Liveness = alive
        ;   fn_rpil_reduced(Func, [L|Args], Rpil),
            memberchk(rpil_kill(Var), Rpil) ->
            (   ctx_typing(StmtsR, Var, Type),
                lives_even_after_killing(Type) ->
                Liveness = alive
            ;   Liveness = dead
            )
        ;   ctx_liveness(StmtsR, Var, Liveness)
        ).

is_alive(Stmts, Var) :-
        ctx_liveness(Stmts, Var, alive).

ctx_borrowing(Stmts, Lhs, Rhs, Kind) :-
        length(Stmts, L), Stmts = [Stmt|StmtsR],
        Stmt = funcall(L, Func, Args),
        fn_rpil_reduced(Func, [L|Args], RpilInsts),
        ctx_liveness(Stmts, Rhs, alive),
        ctx_borrowing_partial(StmtsR, RpilInsts, Lhs, Rhs, Kind).

ctx_borrowing_partial(Stmts, [], Lhs, Rhs, Kind) :-
    !, ctx_borrowing(Stmts, Lhs, Rhs, Kind).
ctx_borrowing_partial(Stmts, Insts, Lhs, Rhs, Kind) :-
        Insts = [Inst|InstsR],
        (   Inst = rpil_borrow(Lhs, Rhs) ->
            Kind = shared
        ;   Inst = rpil_borrow_mut(Lhs, Rhs) ->
            Kind = mutable
        ;   Inst = rpil_bind(PL, PR),
            replace_origin(Lhs, PL, PR, Prev) ->
            ctx_borrowing_partial(Stmts, InstsR, Prev, Rhs, Kind)
        ;   ctx_borrowing_partial(Stmts, InstsR, Lhs, Rhs, Kind)
        ).

replace_origin(X0, X0, Y, Y).
replace_origin(place(X0, P), X, Y, place(Y0, P)) :-
        replace_origin(X0, X, Y, Y0).
replace_origin(deref(X0), X, Y, deref(Y0)) :-
        replace_origin(X0, X, Y, Y0).

well_typed_program(Stmts, Length) :-
        length(Stmts, Length),
        check_all_lines(Stmts, Length).

check_all_lines(_, 0).
check_all_lines(Stmts, L) :-
        ctx_typing(Stmts, L, _),
        LR is L - 1,
        check_all_lines(Stmts, LR).

% =============================================================================

:- begin_tests(rpil).

test(rpil_term_reduction_1) :-
        rpil_term_reduction([5,3], op(0), 5).

test(rpil_term_reduction_2) :-
        rpil_term_reduction([3,2], place(op(0),1), place(3,1)).

test(rpil_inst_reduction_1) :-
        rpil_inst_reduction([5,3], rpil_borrow(op(0),op(1)), rpil_borrow(5,3)).

test(rpil_reduction_1) :-
        rpil_reduction([5,3], [rpil_borrow(op(0),op(1))], [rpil_borrow(5,3)]).

test(fn_rpil_reduced_1) :-
        fn_rpil_reduced(borrow_F, [5|[3]], [rpil_borrow(5,3)]).

test(fn_rpil_reduced_2) :-
        fn_rpil_reduced(move_F, [7|[2]], Insts), !,
        Insts = [rpil_kill(2),rpil_bind(7,2),rpil_move(2)].

:- end_tests(rpil).

:- begin_tests(ctx_typing_liveness).

test(ctx_typing_1) :-
        ctx_typing([funcall(2,unmovable_new_F,[]),_], 2, unmovable_T).

test(ctx_typing_2) :-
        ctx_typing(Stmts, 2, unmovable_T), !,
        Stmts = [funcall(2,unmovable_new_F,[]),_].

test(lives_even_after_killing_1) :-
        lives_even_after_killing(mutref_T(_)).

test(lives_even_after_killing_2) :-
        lives_even_after_killing(option_T(ref_T(_))).

test(lives_even_after_killing_3, [fail]) :-
        lives_even_after_killing(option_T(mutref_T(_))).

test(ctx_liveness_1) :-
        ctx_liveness([funcall(2,move_F,[1])
                     ,funcall(1,unmovable_new_F,[])
                     ], 1, dead).

test(ctx_liveness_2, [fail]) :-
        ctx_liveness([funcall(1,borrow_F,[1])
                     ], 1, _).

test(ctx_liveness_3, [fail]) :-
        ctx_liveness([funcall(2,move_F,[1])
                     ,funcall(1,borrow_F,[1])
                     ], 1, _).

test(ctx_liveness_4) :-
        ctx_liveness([funcall(3,move_F,[2])
                     ,funcall(2,borrow_mut_F,[1])
                     ,funcall(1,unmovable_new_F,[])
                     ], 2, Liveness), !,
        Liveness = alive.

test(ctx_typing_liveness_1) :-
        ctx_typing(Stmts, 2, unmovable_T),
        ctx_liveness(Stmts, 1, dead),
        well_typed_program(Stmts, 2), !,
        Stmts = [funcall(2,move_F,[1])
                ,funcall(1,unmovable_new_F,[])
                ].

:- end_tests(ctx_typing_liveness).

:- begin_tests(ctx_borrowing).

test(ctx_borrowing_partial_1) :-
        ctx_borrowing_partial([], [rpil_borrow(2,1)], 2, 1, shared).

test(ctx_borrowing_partial_2) :-
        ctx_borrowing_partial([funcall(2,borrow_F,[1])
                              ,funcall(1,unmovable_new_F,[])
                              ], [], 2, 1, shared).

text(ctx_borrowing_1) :-
        ctx_borrowing([funcall(1,borrow_F,[1])], 1, 1, shared).

test(ctx_borrowing_2) :-
        ctx_borrowing([funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F,[])
                      ], 2, 1, shared).

test(ctx_borrowing_3) :-
        ctx_borrowing([funcall(3,option_some_F,[2])
                      ,funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F,[])
                      ], 2, 1, shared).

test(ctx_borrowing_4) :-
        ctx_borrowing([funcall(3,option_some_F,[2])
                      ,funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F,[])
                      ], place(3,1), 1, shared).

test(ctx_borrowing_5) :-
        ctx_borrowing(Stmts, place(3,1), 1, shared),
        well_typed_program(Stmts, 3), !,
        Stmts = [funcall(3,option_some_F,[2])
                ,funcall(2,borrow_F,[1])
                ,funcall(1,unmovable_new_F,[])
                ].

test(ctx_borrowing_6) :-
        ctx_borrowing([funcall(4,move_F,[3])
                      ,funcall(3,option_some_F,[2])
                      ,funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F,[])
                      ], place(4,1), 1, shared).

test(ctx_borrowing_7) :-
        ctx_borrowing([funcall(4,option_some_F,[3])
                      ,funcall(3,option_some_F,[2])
                      ,funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F,[])
                      ], place(place(4,1),1), 1, shared).

test(ctx_borrowing_8) :-
        ctx_borrowing([funcall(5,move_F,[4])
                      ,funcall(4,option_some_F,[3])
                      ,funcall(3,option_some_F,[2])
                      ,funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F,[])
                      ], place(place(5,1),1), 1, shared).

:- end_tests(ctx_borrowing).

:- begin_tests(ctx_borrowing_liveness).

test(ctx_borrowing_liveness_1, [fail]) :-
        ctx_borrowing([funcall(3,move_F,[1])
                      ,funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F,[])
                      ], 2, 1, shared).

:- end_tests(ctx_borrowing_liveness).
