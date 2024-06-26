% -*- coding: iso_8859_1 -*-
%
% File: pinchecker_test.pl
% Description: Test cases for module(pinchecker)
%
% Version: 0.3.2
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>

:- use_module(library(plunit)).
:- use_module(pinchecker).

:- multifile pinchecker:fn_typing/3.
:- multifile pinchecker:fn_rpil/2.
:- multifile pinchecker:impl_trait/2.


pinchecker:fn_typing(move_F, [T], T).
pinchecker:fn_typing(borrow_F, [T], ref_T(T)).
pinchecker:fn_typing(borrow_mut_F, [T], mutref_T(T)).
pinchecker:fn_typing(option_some_F, [T], option_T(T)).
pinchecker:fn_typing(option_none_F, [], option_T(_)).
pinchecker:fn_typing(pin_macro_F, [T], pin_T(mutref_T(T))).
pinchecker:fn_typing(unmovable_new_F_testonly, [], unmovable_T_testonly).
pinchecker:fn_typing(borrow_option_p1_F_testonly, [option_T(T)], ref_T(T)).
pinchecker:fn_typing(borrow_mut_option_p1_F_testonly, [option_T(T)], mutref_T(T)).
pinchecker:fn_typing(non_copy_storage_F_testonly, [T], ncs_T_testonly(T)).
pinchecker:fn_typing(pin_new_unchecked_F_testonly, [mutref_T(T)], pin_T(mutref_T(T))).
pinchecker:fn_typing(kill_two_F_testonly, [_, _], unit_T).
pinchecker:fn_typing(move_two_F_testonly, [_, _], unit_T).
pinchecker:fn_typing(borrow_mut_and_pin_F_testonly, [_], unit_T).
pinchecker:fn_typing(pin_and_move_F_testonly, [_], unit_T).
pinchecker:fn_typing(borrow_mut_and_pin_and_move_F_testonly, [_], unit_T).
pinchecker:fn_typing(move_pin_inner_F_testonly, [_], unit_T).
pinchecker:fn_typing(enum_with_3_places_new_F_testonly, [], ew3p_T_testonly).
pinchecker:fn_typing(struct_with_mutref_ew3p_at_p2_new_F_testonly, [mutref_T(ew3p_T_testonly)], smrew3pp2_T_testonly).
pinchecker:fn_typing(extract_mutref_to_ew3p_p3_F_testonly, [mutref_T(smrew3pp2_T_testonly)], mutref_T(ew3p_p3_T)).


pinchecker:fn_rpil(move_F,
        [rpil_kill(op(1))
        ,rpil_bind(op(0), op(1))
        ,rpil_move(op(1))
        ]).
pinchecker:fn_rpil(borrow_F,
        [rpil_borrow(op(0), op(1))
        ]).
pinchecker:fn_rpil(borrow_mut_F,
        [rpil_borrow_mut(op(0), op(1))
        ]).
pinchecker:fn_rpil(option_some_F,
        [rpil_kill(op(1))
        ,rpil_bind(place(op(0),1), op(1))
        ,rpil_move(op(1))
        ]).
pinchecker:fn_rpil(option_none_F,
        []).
pinchecker:fn_rpil(pin_macro_F,
        [rpil_kill(op(1))
        ,rpil_deref_pin(op(0))
        ,rpil_borrow_mut(op(0), place(op(0),0))
        ,rpil_move(op(1))
        ]).
pinchecker:fn_rpil(unmovable_new_F_testonly,
        []).
pinchecker:fn_rpil(borrow_option_p1_F_testonly,
        [rpil_borrow(op(0), place(op(1),1))
        ]).
pinchecker:fn_rpil(borrow_mut_option_p1_F_testonly,
        [rpil_borrow_mut(op(0), place(op(1),1))
        ]).
pinchecker:fn_rpil(non_copy_storage_F_testonly,
        [rpil_kill(op(1))
        ,rpil_bind(place(op(0),1), op(1))
        ,rpil_move(op(1))
        ]).
pinchecker:fn_rpil(pin_new_unchecked_F_testonly,
        [rpil_bind(op(0), op(1))
        ,rpil_deref_pin(op(1))
        ]).
pinchecker:fn_rpil(kill_two_F_testonly,
        [rpil_kill(op(2))
        ,rpil_kill(op(1))
        ]).
pinchecker:fn_rpil(move_two_F_testonly,
        [rpil_move(op(2))
        ,rpil_move(op(1))
        ]).
pinchecker:fn_rpil(borrow_mut_and_pin_F_testonly,
        [rpil_deref_pin(op(0))
        ,rpil_borrow_mut(op(0), op(1))
        ]).
pinchecker:fn_rpil(pin_and_move_F_testonly,
        [rpil_deref_move(op(1))
        ,rpil_deref_pin(op(1))
        ]).
pinchecker:fn_rpil(borrow_mut_and_pin_and_move_F_testonly,
        [rpil_deref_move(op(0))
        ,rpil_deref_pin(op(0))
        ,rpil_borrow_mut(op(0), op(1))
        ]).
pinchecker:fn_rpil(move_pin_inner_F_testonly,
        [rpil_deref_move(op(1))
        ]).
pinchecker:fn_rpil(enum_with_3_places_new_F_testonly,
        []).
pinchecker:fn_rpil(struct_with_mutref_ew3p_at_p2_new_F_testonly,
        [rpil_bind(place(op(0),2), op(1))
        ]).
pinchecker:fn_rpil(extract_mutref_to_ew3p_p3_F_testonly,
        [rpil_borrow_mut(op(0), place(deref(place(deref(op(1)),2)),3))
        ]).


pinchecker:impl_trait(ref_T(_), copy_Tr).
pinchecker:impl_trait(option_T(T), copy_Tr) :- pinchecker:impl_trait(T, copy_Tr).

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
        ctx_typing([funcall(1,unmovable_new_F_testonly,[])], 1, unmovable_T_testonly).

test(ctx_typing_2) :-
        ctx_typing(Stmts, 2, unmovable_T_testonly), !,
        Stmts = [funcall(2,move_F,[1]),funcall(1,unmovable_new_F_testonly,[])].

test(ctx_typing_3) :-
        Stmts = [funcall(3,move_F,[2])
                ,funcall(2,unmovable_new_F_testonly,[])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall(Var, ctx_typing(Stmts, Var, unmovable_T_testonly), [3,2,1]).

test(lives_even_after_killing_1) :-
        lives_even_after_killing(mutref_T(_)).

test(lives_even_after_killing_2) :-
        lives_even_after_killing(option_T(ref_T(_))).

test(lives_even_after_killing_3, [fail]) :-
        lives_even_after_killing(option_T(mutref_T(_))).

test(ctx_liveness_1) :-
        ctx_liveness([funcall(2,move_F,[1])
                     ,funcall(1,unmovable_new_F_testonly,[])
                     ], 1, dead).

test(ctx_liveness_1_neg, [fail]) :-
        ctx_liveness([funcall(2,move_F,[1])
                     ,funcall(1,unmovable_new_F_testonly,[])
                     ], 1, alive).

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
                     ,funcall(1,unmovable_new_F_testonly,[])
                     ], 2, alive).

test(ctx_liveness_4_neg, [fail]) :-
        ctx_liveness([funcall(3,move_F,[2])
                     ,funcall(2,borrow_mut_F,[1])
                     ,funcall(1,unmovable_new_F_testonly,[])
                     ], 2, dead).

test(ctx_liveness_5) :-
        Stmts = [funcall(4,kill_two_F_testonly,[2,3])
                ,funcall(3,borrow_mut_F,[1])
                ,funcall(2,borrow_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall(Var, ctx_liveness(Stmts, Var, alive), [4,3,2,1]),
        findall(Var, ctx_liveness(Stmts, Var, dead), []).

test(ctx_liveness_6) :-
        Stmts = [funcall(3,kill_two_F_testonly,[1,2])
                ,funcall(2,borrow_mut_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall(Var, ctx_liveness(Stmts, Var, alive), [3,2]),
        findall(Var, ctx_liveness(Stmts, Var, dead), [1]).

test(ctx_typing_liveness_1) :-
        length(Stmts, 2),
        ctx_typing(Stmts, 2, unmovable_T_testonly),
        ctx_liveness(Stmts, 1, dead),
        ctx_typing(Stmts, 1, _), !,
        Stmts = [funcall(2,move_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ].

:- end_tests(ctx_typing_liveness).


:- begin_tests(ctx_borrowing).

text(ctx_borrowing_1) :-
        ctx_borrowing([funcall(1,borrow_F,[1])], 1, 1, shared).

test(ctx_borrowing_2) :-
        ctx_borrowing([funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F_testonly,[])
                      ], 2, 1, shared).

test(ctx_borrowing_3) :-
        ctx_borrowing([funcall(3,option_some_F,[2])
                      ,funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F_testonly,[])
                      ], 2, 1, shared).

test(ctx_borrowing_4) :-
        ctx_borrowing([funcall(3,option_some_F,[2])
                      ,funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F_testonly,[])
                      ], place(3,1), 1, shared).

test(ctx_borrowing_5) :-
        length(Stmts, 3),
        ctx_borrowing(Stmts, place(3,1), 1, shared),
        ctx_typing(Stmts, 3, _),
        ctx_typing(Stmts, 2, _),
        ctx_typing(Stmts, 1, _), !,
        Stmts = [funcall(3,option_some_F,[2])
                ,funcall(2,borrow_F,[1])
                ,funcall(1,option_none_F,[])
                ].

test(ctx_borrowing_6) :-
        Stmts = [funcall(4,move_F,[3])
                ,funcall(3,option_some_F,[2])
                ,funcall(2,borrow_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        ctx_borrowing(Stmts, place(4,1), 1, shared).

test(ctx_borrowing_6_enum) :-
        Stmts = [funcall(4,move_F,[3])
                ,funcall(3,option_some_F,[2])
                ,funcall(2,borrow_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[place(4,1),1,shared],[place(3,1),1,shared],[2,1,shared]].

test(ctx_borrowing_7) :-
        ctx_borrowing([funcall(4,option_some_F,[3])
                      ,funcall(3,option_some_F,[2])
                      ,funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F_testonly,[])
                      ], place(place(4,1),1), 1, shared).

test(ctx_borrowing_8) :-
        Stmts = [funcall(5,move_F,[4])
                ,funcall(4,option_some_F,[3])
                ,funcall(3,option_some_F,[2])
                ,funcall(2,borrow_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[place(place(5,1),1),1,shared]
                  ,[place(place(4,1),1),1,shared]
                  ,[place(3,1),1,shared]
                  ,[2,1,shared]
                  ].

test(ctx_borrowing_9) :-
        Stmts = [funcall(2,pin_macro_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[2,place(2,0),mutable]].

test(ctx_borrowing_10) :-
        Stmts = [funcall(3,borrow_mut_option_p1_F_testonly,[2])
                ,funcall(2,option_some_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall(Place, ctx_borrowing(Stmts, 3, Place, mutable), [place(2,1)]).

test(ctx_borrowing_11) :-
        Stmts = [funcall(5,borrow_mut_option_p1_F_testonly,[3])
                ,funcall(4,borrow_F,[1])
                ,funcall(3,option_some_F,[2])
                ,funcall(2,unmovable_new_F_testonly,[])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[5,place(3,1),mutable],[4,1,shared]].

test(ctx_borrowing_12) :-
        Stmts = [funcall(5,extract_mutref_to_ew3p_p3_F_testonly,[4])
                ,funcall(4,borrow_mut_F,[3])
                ,funcall(3,struct_with_mutref_ew3p_at_p2_new_F_testonly,[2])
                ,funcall(2,borrow_mut_F,[1])
                ,funcall(1,enum_with_3_places_new_F_testonly,[])
                ],
        ctx_borrowing(Stmts, 5, place(1,3), mutable).

test(ctx_borrowing_12_enum) :-
        Stmts = [funcall(5,extract_mutref_to_ew3p_p3_F_testonly,[4])
                ,funcall(4,borrow_mut_F,[3])
                ,funcall(3,struct_with_mutref_ew3p_at_p2_new_F_testonly,[2])
                ,funcall(2,borrow_mut_F,[1])
                ,funcall(1,enum_with_3_places_new_F_testonly,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[5,place(1,3),mutable],[4,3,mutable],[place(3,2),1,mutable],[2,1,mutable]].

:- end_tests(ctx_borrowing).


:- begin_tests(follow_deref).

% TODO: This test case currently fails and needs to be fixed
test(follow_deref_1) :-
        Stmts = [funcall(4,borrow_mut_F,[3])
                ,funcall(3,struct_with_mutref_ew3p_at_p2_new_F_testonly,[2])
                ,funcall(2,borrow_mut_F,[1])
                ,funcall(1,enum_with_3_places_new_F_testonly,[])
                ],
        follow_deref(Stmts, [], place(deref(place(deref(X),2)),3), place(1,3)), !,
        X = 4.

:- end_tests(follow_deref).


:- begin_tests(ctx_borrowing_liveness).

test(ctx_borrowing_liveness_1, [fail]) :-
        ctx_borrowing([funcall(3,move_F,[1])
                      ,funcall(2,borrow_F,[1])
                      ,funcall(1,unmovable_new_F_testonly,[])
                      ], 2, 1, shared).

test(ctx_borrowing_liveness_2) :-
        Stmts = [funcall(3,borrow_option_p1_F_testonly,[2])
                ,funcall(2,option_some_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[3,place(2,1),shared]].

test(ctx_borrowing_liveness_3) :-
        Stmts = [funcall(4,non_copy_storage_F_testonly,[3])
                ,funcall(3,borrow_option_p1_F_testonly,[2])
                ,funcall(2,option_some_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[place(4,1),place(2,1),shared],[3,place(2,1),shared]].

test(ctx_borrowing_liveness_4) :-
        Stmts = [funcall(5,move_F,[4])
                ,funcall(4,non_copy_storage_F_testonly,[3])
                ,funcall(3,borrow_option_p1_F_testonly,[2])
                ,funcall(2,option_some_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[place(5,1),place(2,1),shared],[3,place(2,1),shared]].

test(ctx_borrowing_liveness_4_neg, [fail]) :-
        Stmts = [funcall(5,move_F,[4])
                ,funcall(4,non_copy_storage_F_testonly,[3])
                ,funcall(3,borrow_option_p1_F_testonly,[2])
                ,funcall(2,option_some_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        ctx_borrowing(Stmts, place(4,1), place(2,1), _).

:- end_tests(ctx_borrowing_liveness).


:- begin_tests(ctx_pinning).

test(ctx_pinning_unpinned_1) :-
        Stmts = [funcall(2,borrow_mut_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        ctx_pinning(Stmts, 1, unpinned), !, Stmts = [_|StmtsR],
        \+ ctx_pinning(StmtsR, _, _).

test(ctx_pinning_1) :-
        Stmts = [funcall(3,pin_new_unchecked_F_testonly,[2])
                ,funcall(2,borrow_mut_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        ctx_pinning(Stmts, 1, pinned).

test(ctx_pinning_1_enum) :-
        Stmts = [funcall(3,pin_new_unchecked_F_testonly,[2])
                ,funcall(2,borrow_mut_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Place, Status], ctx_pinning(Stmts, Place, Status), Results), !,
        Results = [[1,pinned]].

test(ctx_pinning_2) :-
        Stmts = [funcall(4,move_F,[1])
                ,funcall(3,pin_new_unchecked_F_testonly,[2])
                ,funcall(2,borrow_mut_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        ctx_pinning(Stmts, 1, moved).

test(ctx_pinning_2_enum) :-
        Stmts = [funcall(4,move_F,[1])
                ,funcall(3,pin_new_unchecked_F_testonly,[2])
                ,funcall(2,borrow_mut_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Place, Status], ctx_pinning(Stmts, Place, Status), Results), !,
        Results = [[1,moved]].

test(ctx_pinning_3) :-
        Stmts = [funcall(6,pin_new_unchecked_F_testonly,[4])
                ,funcall(5,borrow_mut_option_p1_F_testonly,[3])
                ,funcall(4,borrow_mut_F,[1])
                ,funcall(3,option_some_F,[2])
                ,funcall(2,unmovable_new_F_testonly,[])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Place, Status], ctx_pinning(Stmts, Place, Status), Results), !,
        Results = [[place(3,1),unpinned],[1,pinned]].

test(ctx_pinning_4) :-
        Stmts = [funcall(7,pin_new_unchecked_F_testonly,[5])
                ,funcall(6,pin_new_unchecked_F_testonly,[4])
                ,funcall(5,borrow_mut_option_p1_F_testonly,[3])
                ,funcall(4,borrow_mut_F,[1])
                ,funcall(3,option_some_F,[2])
                ,funcall(2,unmovable_new_F_testonly,[])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Place, Status], ctx_pinning(Stmts, Place, Status), Results), !,
        Results = [[place(3,1),pinned],[1,pinned]].

test(ctx_pinning_5) :-
        Stmts = [funcall(6,pin_and_move_F_testonly,[5])
                ,funcall(5,borrow_mut_option_p1_F_testonly,[3])
                ,funcall(4,borrow_mut_F,[1])
                ,funcall(3,option_some_F,[2])
                ,funcall(2,unmovable_new_F_testonly,[])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Place, Status], ctx_pinning(Stmts, Place, Status), Results), !,
        Results = [[place(3,1),moved],[1,unpinned]].

test(ctx_pinning_6) :-
        Stmts = [funcall(3,move_pin_inner_F_testonly,[2])
                ,funcall(2,pin_macro_F,[1])
                ,funcall(1,unmovable_new_F_testonly,[])
                ],
        findall([Place, Status], ctx_pinning(Stmts, Place, Status), Results), !,
        Results = [[place(2,0),moved]].

test(ctx_pinning_7) :-
        Stmts = [funcall(6,pin_new_unchecked_F_testonly,[5])
                ,funcall(5,extract_mutref_to_ew3p_p3_F_testonly,[4])
                ,funcall(4,borrow_mut_F,[3])
                ,funcall(3,struct_with_mutref_ew3p_at_p2_new_F_testonly,[2])
                ,funcall(2,borrow_mut_F,[1])
                ,funcall(1,enum_with_3_places_new_F_testonly,[])
                ],
        findall([Place, Status], ctx_pinning(Stmts, Place, Status), Results), !,
        Results = [[place(1,3),pinned],[3,unpinned],[1,unpinned]].

test(ctx_pinning_generate_1) :-
        length(Stmts, 2),
        ctx_pinning(Stmts, 1, pinned),
        ctx_typing(Stmts, 2, _),
        ctx_typing(Stmts, 1, _), !,
        Stmts = [funcall(2,borrow_mut_and_pin_F_testonly,[1])
                ,funcall(1,option_none_F,[])].

test(ctx_pinning_generate_2) :-
        length(Stmts, 2),
        ctx_pinning(Stmts, 1, moved),
        ctx_typing(Stmts, 2, _),
        ctx_typing(Stmts, 1, _), !,
        Stmts = [funcall(2,borrow_mut_and_pin_and_move_F_testonly,[1])
                ,funcall(1,option_none_F,[])].

:- end_tests(ctx_pinning).
