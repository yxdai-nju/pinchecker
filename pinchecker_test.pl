% -*- coding: iso_8859_1 -*-
%
% File: pinchecker_test.pl
% Description: Test cases for module(pinchecker)
%
% Version: 0.4.0
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>

:- use_module(library(plunit)).
:- use_module(pinchecker).

:- multifile pinchecker:fn_typing/3.
:- multifile pinchecker:fn_rpil/2.
:- multifile pinchecker:impl_trait/2.
:- multifile pinchecker:does_not_kill_arguments/1.


pinchecker:fn_typing(move_F, [T], T).
pinchecker:fn_typing(deref_move_F, [mutref_T(_)], unit_T).
pinchecker:fn_typing(borrow_F, [T], ref_T(T)).
pinchecker:fn_typing(borrow_mut_F, [T], mutref_T(T)).
pinchecker:fn_typing(option_some_F, [T], option_T(T)).
pinchecker:fn_typing(option_none_F, [], option_T(_)).
pinchecker:fn_typing(pin_macro_F, [T], pin_T(mutref_T(T))).
pinchecker:fn_typing(unmovable_new_F, [], unmovable_T).
pinchecker:fn_typing(borrow_mut_option_p1_F, [mutref_T(option_T(T))], mutref_T(T)).
pinchecker:fn_typing(store_new_F, [T], store_T(T)).
pinchecker:fn_typing(pin_new_unchecked_F, [Ptr], pin_T(Ptr)) :-
        pinchecker:impl_trait(Ptr, deref_Tr(_)).
pinchecker:fn_typing(kill_two_F, [_, _], unit_T).
pinchecker:fn_typing(store_two_new_F, [T1, T2], store_two_T(T1, T2)).
pinchecker:fn_typing(ew3p_new_F, [], ew3p_T).
pinchecker:fn_typing(mr_ew3p_p2_new_F, [mutref_T(ew3p_T)], mr_ew3p_p2_T).
pinchecker:fn_typing(borrow_mut_p2_p3_F, [mutref_T(mr_ew3p_p2_T)], mutref_T(ew3p_p3_T)).


pinchecker:fn_rpil(move_F,
        [ rpil_bind(arg(0), arg(1))
        , rpil_move(arg(1))
        ]).
pinchecker:fn_rpil(deref_move_F,
        [ rpil_deref_move(arg(1))
        ]).
pinchecker:fn_rpil(borrow_F,
        [ rpil_borrow(arg(0), arg(1))
        ]).
pinchecker:fn_rpil(borrow_mut_F,
        [ rpil_borrow_mut(arg(0), arg(1))
        ]).
pinchecker:fn_rpil(option_some_F,
        [ rpil_bind(place(arg(0),1), arg(1))
        , rpil_move(arg(1))
        ]).
pinchecker:fn_rpil(option_none_F,
        [ ]).
pinchecker:fn_rpil(pin_macro_F,
        [ rpil_deref_pin(arg(0))
        , rpil_borrow_mut(arg(0), place_ext(arg(0)))
        , rpil_move(arg(1))
        ]).
pinchecker:fn_rpil(unmovable_new_F,
        [ ]).
pinchecker:fn_rpil(borrow_mut_option_p1_F,
        [ rpil_borrow_mut(arg(0), place(deref(arg(1)),1))
        ]).
pinchecker:fn_rpil(store_new_F,
        [ rpil_bind(place(arg(0),1), arg(1))
        , rpil_move(arg(1))
        ]).
pinchecker:fn_rpil(pin_new_unchecked_F,
        [ rpil_bind(arg(0), arg(1))
        , rpil_deref_pin(arg(1))
        ]).
pinchecker:fn_rpil(kill_two_F,
        [ ]).
pinchecker:fn_rpil(store_two_new_F,
        [ rpil_bind(place(arg(0),2), arg(2))
        , rpil_move(arg(2))
        , rpil_bind(place(arg(0),1), arg(1))
        , rpil_move(arg(1))
        ]).
pinchecker:fn_rpil(ew3p_new_F,
        [ ]).
pinchecker:fn_rpil(mr_ew3p_p2_new_F,
        [ rpil_bind(place(arg(0),2), arg(1))
        ]).
pinchecker:fn_rpil(borrow_mut_p2_p3_F,
        [ rpil_borrow_mut(arg(0), place(deref(place(deref(arg(1)),2)),3))
        ]).


pinchecker:impl_trait(ref_T(_), copy_Tr) :- !.
pinchecker:impl_trait(option_T(T), copy_Tr) :-
        pinchecker:impl_trait(T, copy_Tr).
pinchecker:impl_trait(ref_T(T), deref_Tr(target(T))).
pinchecker:impl_trait(mutref_T(T), deref_Tr(target(T))).
pinchecker:impl_trait(mutref_T(T), derefmut_Tr(target(T))).


pinchecker:does_not_kill_arguments(borrow_F).
pinchecker:does_not_kill_arguments(borrow_mut_F).

% =============================================================================

:- begin_tests(rpil).

test(rpil_term_reduction_1) :-
        rpil_term_reduction([5, 3], arg(0), variable(5)).

test(rpil_term_reduction_2) :-
        rpil_term_reduction([3, 2], place(arg(0),1), place(variable(3),1)).

test(rpil_inst_reduction_1) :-
        rpil_inst_reduction([5, 3], rpil_borrow(arg(0), arg(1)), rpil_borrow(variable(5), variable(3))).

test(rpil_reduction_1) :-
        rpil_reduction([5, 3], [rpil_borrow(arg(0), arg(1))], [rpil_borrow(variable(5), variable(3))]).

test(fn_rpil_reduced_1) :-
        fn_rpil_reduced(borrow_F, [5 | [3]], [rpil_borrow(variable(5), variable(3))]).

test(fn_rpil_reduced_2) :-
        fn_rpil_reduced(move_F, [7 | [2]], [rpil_bind(variable(7), variable(2)), rpil_move(variable(2))]).

:- end_tests(rpil).


:- begin_tests(ctx_typing).

test(ctx_typing_1, [nondet]) :-
        Stmts = [rs_stmt(1,unmovable_new_F,[])],
        ctx_typing(Stmts, 1, unmovable_T).

test(ctx_typing_2) :-
        ctx_typing(Stmts, 2, unmovable_T), !,
        Stmts = [rs_stmt(2,move_F,[1]),rs_stmt(1,unmovable_new_F,[])].

test(ctx_typing_3) :-
        Stmts = [rs_stmt(3,move_F,[2])
                ,rs_stmt(2,unmovable_new_F,[])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall(Var, ctx_typing(Stmts, Var, unmovable_T), [3,2,1]).

% [Expected Behevior] This is intentional
test(ctx_typing_4, [nondet]) :-
        Stmts = [rs_stmt(2,store_two_new_F,[1,1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        ctx_typing(Stmts, 2, store_two_T(unmovable_T, unmovable_T)).

% [Expected Behevior] This is intentional
test(ctx_typing_5, [nondet]) :-
        Stmts = [rs_stmt(3,store_two_new_F,[1,2])
                ,rs_stmt(2,borrow_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        ctx_typing(Stmts, 3, store_two_T(unmovable_T, ref_T(unmovable_T))).

test(ctx_typing_6, [fail]) :-
        Stmts = [rs_stmt(1,borrow_F,[1])
                ],
        ctx_typing(Stmts, 1, _Type).

test(ctx_typing_7, [fail]) :-
        Stmts = [rs_stmt(3,borrow_F,[1])
                ,rs_stmt(2,move_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        ctx_typing(Stmts, 3, _Type).

test(ctx_typing_trait_1) :-
        Stmts = [rs_stmt(3,pin_new_unchecked_F,[2])
                ,rs_stmt(2,borrow_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])],
        findall([Var, Type], ctx_typing(Stmts, Var, Type), Results), !,
        Results = [[3,pin_T(ref_T(unmovable_T))]
                  ,[2,ref_T(unmovable_T)]
                  ,[1,unmovable_T]
                  ].

:- end_tests(ctx_typing).


:- begin_tests(ctx_liveness).

test(lives_even_after_killing_1) :-
        lives_even_after_killing(mutref_T(_)).

test(lives_even_after_killing_2) :-
        lives_even_after_killing(option_T(ref_T(_))).

test(lives_even_after_killing_3, [fail]) :-
        lives_even_after_killing(option_T(mutref_T(_))).

test(ctx_liveness_1) :-
        Stmts = [rs_stmt(2,move_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall(Liveness, ctx_liveness(Stmts, 1, Liveness), Results), !,
        Results = [dead].

test(ctx_liveness_2, [fail]) :-
        Stmts = [rs_stmt(1,borrow_F,[1])],
        ctx_liveness(Stmts, 1, _Liveness).

test(ctx_liveness_3, [fail]) :-
        Stmts = [rs_stmt(2,move_F,[1])
                ,rs_stmt(1,borrow_F,[1])
                ],
        ctx_liveness(Stmts, 1, _Liveness).

test(ctx_liveness_4) :-
        Stmts = [rs_stmt(3,move_F,[2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall(Liveness, ctx_liveness(Stmts, 2, Liveness), Results), !,
        Results = [alive].

test(ctx_liveness_5) :-
        Stmts = [rs_stmt(4,kill_two_F,[2,3])
                ,rs_stmt(3,borrow_mut_F,[1])
                ,rs_stmt(2,borrow_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall(Var, ctx_liveness(Stmts, Var, alive), [4,3,2,1]),
        findall(Var, ctx_liveness(Stmts, Var, dead), []).

test(ctx_liveness_6) :-
        Stmts = [rs_stmt(3,kill_two_F,[1,2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall(Var, ctx_liveness(Stmts, Var, alive), [3,2]),
        findall(Var, ctx_liveness(Stmts, Var, dead), [1]).

% [Expected Behevior] The reference stays alive even if the referenced variable is killed
test(ctx_liveness_7) :-
        Stmts = [rs_stmt(3,move_F,[1])
                ,rs_stmt(2,borrow_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall(Var, ctx_liveness(Stmts, Var, alive), [3,2]),
        findall(Var, ctx_liveness(Stmts, Var, dead), [1]).

test(ctx_liveness_gen_1) :-
        length(Stmts, 2),
        ctx_typing(Stmts, 2, unmovable_T),
        ctx_liveness(Stmts, 1, dead),
        ctx_typing(Stmts, 2, _),
        ctx_typing(Stmts, 1, _), !,
        Stmts = [rs_stmt(2,move_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ].

:- end_tests(ctx_liveness).


:- begin_tests(follow_deref).

test(ctx_borrowing_follow_deref_1, [fail]) :-
        ctx_borrowing([funcall(1,borrow_F,[_])], _Lhs, _Rhs, _Kind).

test(ctx_pinning_follow_deref_1, [fail]) :-
        ctx_pinning([funcall(1,borrow_F,[_])], _Op, _Status).

test(follow_deref_1) :-
        Stmts = [rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,mr_ew3p_p2_new_F,[2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,ew3p_new_F,[])
                ],
        follow_deref(Stmts, [], place(deref(place(deref(Op),2)),3), place(variable(1),3)), !,
        Op = variable(4).

:- end_tests(follow_deref).


:- begin_tests(ctx_borrowing).

test(ctx_borrowing_1, [fail]) :-
        Stmts = [rs_stmt(1,borrow_F,[1])],
        ctx_borrowing(Stmts, variable(1), variable(1), shared).

test(ctx_borrowing_2) :-
        Stmts = [rs_stmt(2,borrow_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs ,Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[variable(2),variable(1),shared]].

test(ctx_borrowing_3) :-
        Stmts = [rs_stmt(3,option_some_F,[2])
                ,rs_stmt(2,borrow_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[place(variable(3),1),variable(1),shared]
                 ,[variable(2),variable(1),shared]].

test(ctx_borrowing_4) :-
        Stmts = [rs_stmt(5,move_F,[4])
                ,rs_stmt(4,option_some_F,[3])
                ,rs_stmt(3,option_some_F,[2])
                ,rs_stmt(2,borrow_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[place(place(variable(5),1),1),variable(1),shared]
                 ,[place(place(variable(4),1),1),variable(1),shared]
                 ,[place(variable(3),1),variable(1),shared]
                 ,[variable(2),variable(1),shared]].

test(ctx_borrowing_5) :-
        Stmts = [rs_stmt(2,pin_macro_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[variable(2),place_ext(variable(2)),mutable]].

test(ctx_borrowing_6) :-
        Stmts = [rs_stmt(4,borrow_mut_option_p1_F,[3])
                ,rs_stmt(3,borrow_mut_F,[2])
                ,rs_stmt(2,option_some_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[variable(4),place(variable(2),1),mutable]
                 ,[variable(3),variable(2),mutable]].

test(ctx_borrowing_7) :-
        Stmts = [rs_stmt(5,borrow_mut_p2_p3_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,mr_ew3p_p2_new_F,[2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,ew3p_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[variable(5),place(variable(1),3),mutable]
                 ,[variable(4),variable(3),mutable]
                 ,[place(variable(3),2),variable(1),mutable]
                 ,[variable(2),variable(1),mutable]].

test(ctx_borrowing_gen_1) :-
        length(Stmts, 3),
        ctx_borrowing(Stmts, place(variable(3),1), variable(1), shared),
        ctx_typing(Stmts, 3, _),
        ctx_typing(Stmts, 2, _),
        ctx_typing(Stmts, 1, _), !,
        Stmts = [rs_stmt(3,option_some_F,[2])
                ,rs_stmt(2,borrow_F,[1])
                ,rs_stmt(1,option_none_F,[])].

test(ctx_borrowing_gen_2) :-
        Stmts = [S5
                ,S4
                ,S3
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,ew3p_new_F,[])
                ],
        ctx_borrowing(Stmts, variable(5), place(variable(1),3), mutable),
        ctx_typing(Stmts, 5, _),
        ctx_typing(Stmts, 4, _),
        ctx_typing(Stmts, 3, _), !,
        S5 = rs_stmt(5,borrow_mut_p2_p3_F,[4]),
        S4 = rs_stmt(4,borrow_mut_F,[3]),
        S3 = rs_stmt(3,mr_ew3p_p2_new_F,[2]).

test(ctx_borrowing_gen_2_full) :-
        length(Stmts, 5),
        ctx_borrowing(Stmts, variable(5), place(variable(1),3), mutable),
        ctx_typing(Stmts, 5, _),
        ctx_typing(Stmts, 4, _),
        ctx_typing(Stmts, 3, _),
        ctx_typing(Stmts, 2, _),
        ctx_typing(Stmts, 1, _), !,
        Stmts = [rs_stmt(5,borrow_mut_p2_p3_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,mr_ew3p_p2_new_F,[2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,ew3p_new_F,[])].

:- end_tests(ctx_borrowing).


:- begin_tests(ctx_borrowing_liveness).

test(ctx_borrowing_liveness_1) :-
        Stmts = [rs_stmt(3,move_F,[1])
                ,rs_stmt(2,borrow_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [].

test(ctx_borrowing_liveness_2) :-
        Stmts = [rs_stmt(5,store_new_F,[4])
                ,rs_stmt(4,borrow_mut_option_p1_F,[3])
                ,rs_stmt(3,borrow_mut_F,[2])
                ,rs_stmt(2,option_some_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[place(variable(5),1),place(variable(2),1),mutable]
                  ,[variable(4),place(variable(2),1),mutable]
                  ,[variable(3),variable(2),mutable]].

test(ctx_borrowing_liveness_3) :-
        Stmts = [rs_stmt(6,move_F,[5])
                ,rs_stmt(5,store_new_F,[4])
                ,rs_stmt(4,borrow_mut_option_p1_F,[3])
                ,rs_stmt(3,borrow_mut_F,[2])
                ,rs_stmt(2,option_some_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[place(variable(6),1),place(variable(2),1),mutable]
                  ,[variable(4),place(variable(2),1),mutable]
                  ,[variable(3),variable(2),mutable]].

:- end_tests(ctx_borrowing_liveness).


:- begin_tests(ctx_pinning).

test(ctx_pinning_1) :-
        Stmts = [rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Op, Status], ctx_pinning(Stmts, Op, Status), Results), !,
        Results = [].

test(ctx_pinning_2) :-
        Stmts = [rs_stmt(3,pin_new_unchecked_F,[2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Op, Status], ctx_pinning(Stmts, Op, Status), Results), !,
        Results = [[variable(1),pinned]].

test(ctx_pinning_3) :-
        Stmts = [rs_stmt(4,deref_move_F,[2])
                ,rs_stmt(3,pin_new_unchecked_F,[2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Op, Status], ctx_pinning(Stmts, Op, Status), Results), !,
        Results = [[variable(1),moved]].

test(ctx_pinning_4) :-
        Stmts = [rs_stmt(5,pin_new_unchecked_F,[2])
                ,rs_stmt(4,deref_move_F,[2])
                ,rs_stmt(3,pin_new_unchecked_F,[2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Op, Status], ctx_pinning(Stmts, Op, Status), Results), !,
        Results = [[variable(1),moved]].

test(ctx_pinning_5) :-
        Stmts = [rs_stmt(6,pin_new_unchecked_F,[5])
                ,rs_stmt(5,borrow_mut_p2_p3_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,mr_ew3p_p2_new_F,[2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,ew3p_new_F,[])
                ],
        findall([Op, Status], ctx_pinning(Stmts, Op, Status), Results), !,
        Results = [[place(variable(1),3),pinned]].

test(ctx_pinning_6) :-
        Stmts = [rs_stmt(7,move_F,[1])
                ,rs_stmt(6,pin_new_unchecked_F,[5])
                ,rs_stmt(5,borrow_mut_p2_p3_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,mr_ew3p_p2_new_F,[2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,ew3p_new_F,[])
                ],
        findall([Op, Status], ctx_pinning(Stmts, Op, Status), Results), !,
        Results = [[place(variable(1),3),moved]].

test(ctx_pinning_gen_1) :-
        Stmts = [S7
                ,S6
                ,S5
                ,S4
                ,rs_stmt(3,mr_ew3p_p2_new_F,[2])
                ,rs_stmt(2,borrow_mut_F,[1])
                ,rs_stmt(1,ew3p_new_F,[])
                ],
        ctx_pinning(Stmts, place(variable(1),3), moved),
        ctx_typing(Stmts, 7, _),
        ctx_typing(Stmts, 6, _),
        ctx_typing(Stmts, 5, _), !,
        S7 = rs_stmt(7,move_F,[1]),
        S6 = rs_stmt(6,pin_new_unchecked_F,[5]),
        S5 = rs_stmt(5,borrow_mut_p2_p3_F,[4]),
        S4 = rs_stmt(4,borrow_mut_F,[3]).

:- end_tests(ctx_pinning).
