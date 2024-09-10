% -*- coding: iso_8859_1 -*-
%
% File: pinchecker_test_realworkd_moveit.pl
% Description: Test case `realworld_moveit` for module(pinchecker)
%
% Version: 0.4.1
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>

:- use_module(library(plunit)).
:- use_module(pinchecker).

:- multifile pinchecker:fn_typing/3.
:- multifile pinchecker:fn_rpil/2.
:- multifile pinchecker:impl_trait/2.
:- multifile pinchecker:does_not_kill_arguments/1.


pinchecker:fn_typing(deref_move_F, [mutref_T(_)], unit_T).
pinchecker:fn_typing(borrow_mut_F, [T], mutref_T(T)).
pinchecker:fn_typing(box_pin_F, [T], pin_T(box_T(T))).
pinchecker:fn_typing(slotdropper_new_F, [], slotdropper_T(_)).
pinchecker:fn_typing(new_unchecked_hygine_hack_F, [mutref_T(slotdropper_T(T))], droppingslot_T(T)).
pinchecker:fn_typing(deref_move_deref_move_F, [pin_T(box_T(T)), droppingslot_T(box_T(maybeuninit_T(T)))], moveref_T(T)).
pinchecker:fn_typing(deref_move_deref_mut_F, [moveref_T(T)], mutref_T(T)).
pinchecker:fn_typing(unmovable_new_F, [], unmovable_T).


pinchecker:fn_rpil(deref_move_F,
        [ rpil_deref_move(arg(1))
        ]).
pinchecker:fn_rpil(borrow_mut_F,
        [ rpil_borrow_mut(arg(0), arg(1))
        ]).
pinchecker:fn_rpil(box_pin_F,
        [ rpil_deref_pin(arg(0))
        , rpil_borrow_mut(arg(0), place_ext(arg(0)))
        , rpil_bind(place_ext(arg(0)), arg(1))
        ]).
pinchecker:fn_rpil(slotdropper_new_F,
        [ ]).
pinchecker:fn_rpil(new_unchecked_hygine_hack_F,
        [ rpil_borrow_mut(place(arg(0),1), place(deref(arg(1)),1))
        ]).
pinchecker:fn_rpil(deref_move_deref_move_F,
        [ rpil_borrow_mut(place(arg(0),3), deref(arg(1)))
        ]).
pinchecker:fn_rpil(deref_move_deref_mut_F,
        [ rpil_borrow_mut(arg(0), deref(place(arg(1),3)))
        ]).
pinchecker:fn_rpil(unmovable_new_F,
        [ ]).


pinchecker:impl_trait(ref_T(_), copy_Tr) :- !.
pinchecker:impl_trait(mutref_T(T), deref_Tr(target(T))).
pinchecker:impl_trait(mutref_T(T), derefmut_Tr(target(T))).


pinchecker:does_not_kill_arguments(borrow_mut_F).

% =============================================================================

:- begin_tests(realworld_moveit).

test(realworld_moveit_typing, [nondet]) :-
        Stmts = [rs_stmt(8,deref_move_F,[7])
                ,rs_stmt(7,deref_move_deref_mut_F,[6])
                ,rs_stmt(6,deref_move_deref_move_F,[2,5])
                ,rs_stmt(5,new_unchecked_hygine_hack_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,slotdropper_new_F,[])
                ,rs_stmt(2,box_pin_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        ctx_typing(Stmts, 8, _),
        ctx_typing(Stmts, 7, _),
        ctx_typing(Stmts, 6, _),
        ctx_typing(Stmts, 5, _),
        ctx_typing(Stmts, 4, _),
        ctx_typing(Stmts, 3, _),
        ctx_typing(Stmts, 2, _),
        ctx_typing(Stmts, 1, _).

test(realworld_moveit_borrowing_1) :-
        Stmts = [rs_stmt(5,new_unchecked_hygine_hack_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,slotdropper_new_F,[])
                ,rs_stmt(2,box_pin_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[place(variable(5),1),place(variable(3),1),mutable]
                  ,[variable(4),variable(3),mutable]
                  ,[variable(2),place_ext(variable(2)),mutable]].

test(realworld_moveit_borrowing_2) :-
        Stmts = [rs_stmt(6,deref_move_deref_move_F,[2,5])
                ,rs_stmt(5,new_unchecked_hygine_hack_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,slotdropper_new_F,[])
                ,rs_stmt(2,box_pin_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[place(variable(6),3),place_ext(variable(2)),mutable]
                  ,[variable(4),variable(3),mutable]].

test(realworld_moveit_borrowing_3) :-
        Stmts = [rs_stmt(7,deref_move_deref_mut_F,[6])
                ,rs_stmt(6,deref_move_deref_move_F,[2,5])
                ,rs_stmt(5,new_unchecked_hygine_hack_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,slotdropper_new_F,[])
                ,rs_stmt(2,box_pin_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs, Kind], ctx_borrowing(Stmts, Lhs, Rhs, Kind), Results), !,
        Results = [[variable(7),place_ext(variable(2)),mutable]
                  ,[variable(4),variable(3),mutable]].

test(realworld_moveit_pinning_1) :-
        Stmts = [rs_stmt(2,box_pin_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Op, Status], ctx_pinning(Stmts, Op, Status), Results), !,
        Results = [[place_ext(variable(2)),pinned]].

test(realworld_moveit_pinning_2) :-
        Stmts = [rs_stmt(8,deref_move_F,[7])
                ,rs_stmt(7,deref_move_deref_mut_F,[6])
                ,rs_stmt(6,deref_move_deref_move_F,[2,5])
                ,rs_stmt(5,new_unchecked_hygine_hack_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,slotdropper_new_F,[])
                ,rs_stmt(2,box_pin_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Op, Status], ctx_pinning(Stmts, Op, Status), Results), !,
        Results = [[place_ext(variable(2)),moved]].

test(realworld_moveit_gen_1) :-
        Stmts = [S8
                ,rs_stmt(7,deref_move_deref_mut_F,[6])
                ,rs_stmt(6,deref_move_deref_move_F,[2,5])
                ,rs_stmt(5,new_unchecked_hygine_hack_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,slotdropper_new_F,[])
                ,rs_stmt(2,box_pin_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        ctx_pinning(Stmts, Op, moved),
        ctx_typing(Stmts, 8, _), !,
        Op = place_ext(variable(2)),
        S8 = rs_stmt(8,deref_move_F,[7]).

test(realworld_moveit_gen_2) :-
        Stmts = [S8
                ,S7
                ,S6
                ,S5
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,slotdropper_new_F,[])
                ,rs_stmt(2,box_pin_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        ctx_pinning(Stmts, Op, moved),
        ctx_typing(Stmts, 8, _),
        ctx_typing(Stmts, 7, _),
        ctx_typing(Stmts, 6, _),
        ctx_typing(Stmts, 5, _),!,
        Op = place_ext(variable(2)),
        S8 = rs_stmt(8,deref_move_F,[7]),
        S7 = rs_stmt(7,deref_move_deref_mut_F,[6]),
        S6 = rs_stmt(6,deref_move_deref_move_F,[2,5]),
        S5 = rs_stmt(5,new_unchecked_hygine_hack_F,[4]).

test(realworld_moveit_gen_3, [nondet]) :-
        Stmts = [_S8
                ,_S7
                ,_S6
                ,_S5
                ,_S4
                ,_S3
                ,_S2
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        ctx_pinning(Stmts, _Op, moved),
        ctx_typing(Stmts, 8, _),
        ctx_typing(Stmts, 7, _),
        ctx_typing(Stmts, 6, _),
        ctx_typing(Stmts, 5, _),
        ctx_typing(Stmts, 4, _),
        ctx_typing(Stmts, 3, _),
        ctx_typing(Stmts, 2, _).

:- end_tests(realworld_moveit).
