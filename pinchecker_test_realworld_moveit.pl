% -*- coding: iso_8859_1 -*-
%
% File: pinchecker_test_realworld_moveit.pl
% Description: Test case `realworld_moveit` for module(pinchecker)
%
% Version: 0.5.0
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>

:- use_module(library(plunit)).
:- use_module(pinchecker).

:- multifile pinchecker:fn_typing/3.
:- multifile pinchecker:fn_rpil/2.


pinchecker:fn_typing(deref_move_F, [mutref_T(_)], unit_T).
pinchecker:fn_typing(borrow_F, [T], ref_T(T)).
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
pinchecker:fn_rpil(borrow_F,
        [ rpil_borrow(arg(0), arg(1))
        ]).
pinchecker:fn_rpil(borrow_mut_F,
        [ rpil_borrow(arg(0), arg(1))
        ]).
pinchecker:fn_rpil(box_pin_F,
        [ rpil_deref_pin(arg(0))
        , rpil_borrow(arg(0), place_ext(arg(0)))
        , rpil_bind(place_ext(arg(0)), arg(1))
        ]).
pinchecker:fn_rpil(slotdropper_new_F,
        [ ]).
pinchecker:fn_rpil(new_unchecked_hygine_hack_F,
        [ rpil_borrow(place(arg(0),1), place(deref(arg(1)),1))
        ]).
pinchecker:fn_rpil(deref_move_deref_move_F,
        [ rpil_borrow(place(arg(0),3), deref(arg(1)))
        ]).
pinchecker:fn_rpil(deref_move_deref_mut_F,
        [ rpil_borrow(arg(0), deref(place(arg(1),3)))
        ]).
pinchecker:fn_rpil(unmovable_new_F,
        [ ]).


pinchecker:ty_typing(pin_T(box_T(T)), ext, T).
pinchecker:ty_typing(slotdropper_T(T), 1, maybe_uninit_T(T)).
pinchecker:ty_typing(slotdropper_T(_), 2, quiet_flag_T).
pinchecker:ty_typing(droppingslot_T(T), 1, mutref_T(maybe_uninit_T(T))).
pinchecker:ty_typing(droppingslot_T(_), 2, dropflag_T).


pinchecker:ty_impl_trait(unmovable_T, non_unpin_Tr).


pinchecker:lives_even_after_killing(ref_T(_)).
pinchecker:lives_even_after_killing(mutref_T(_)).


pinchecker:does_not_kill_arguments(borrow_F).
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
        findall([Lhs, Rhs], ctx_borrowing(Stmts, Lhs, Rhs), Results), !,
        Results = [[place(variable(5),1),place(variable(3),1)]
                  ,[variable(4),variable(3)]
                  ,[variable(2),place_ext(variable(2))]].

test(realworld_moveit_borrowing_2) :-
        Stmts = [rs_stmt(6,deref_move_deref_move_F,[2,5])
                ,rs_stmt(5,new_unchecked_hygine_hack_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,slotdropper_new_F,[])
                ,rs_stmt(2,box_pin_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs], ctx_borrowing(Stmts, Lhs, Rhs), Results), !,
        Results = [[place(variable(6),3),place_ext(variable(2))]
                  ,[place(variable(5),1),place(variable(3),1)]
                  ,[variable(4),variable(3)]
                  ,[variable(2),place_ext(variable(2))]].

test(realworld_moveit_borrowing_3) :-
        Stmts = [rs_stmt(7,deref_move_deref_mut_F,[6])
                ,rs_stmt(6,deref_move_deref_move_F,[2,5])
                ,rs_stmt(5,new_unchecked_hygine_hack_F,[4])
                ,rs_stmt(4,borrow_mut_F,[3])
                ,rs_stmt(3,slotdropper_new_F,[])
                ,rs_stmt(2,box_pin_F,[1])
                ,rs_stmt(1,unmovable_new_F,[])
                ],
        findall([Lhs, Rhs], ctx_borrowing(Stmts, Lhs, Rhs), Results), !,
        Results = [[variable(7),place_ext(variable(2))]
                  ,[place(variable(6),3),place_ext(variable(2))]
                  ,[place(variable(5),1),place(variable(3),1)]
                  ,[variable(4),variable(3)]
                  ,[variable(2),place_ext(variable(2))]].

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
        Results = [[place_ext(variable(2)),pinned_moved]].

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
        ctx_pinning(Stmts, Op, pinned_moved),
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
        ctx_pinning(Stmts, Op, pinned_moved),
        ctx_typing(Stmts, 8, _),
        ctx_typing(Stmts, 7, _),
        ctx_typing(Stmts, 6, _),
        ctx_typing(Stmts, 5, _), !,
        Op = place_ext(variable(2)),
        S8 = rs_stmt(8,deref_move_F,[7]),
        S7 = rs_stmt(7,deref_move_deref_mut_F,[6]),
        S6 = rs_stmt(6,deref_move_deref_move_F,[2,5]),
        S5 = rs_stmt(5,new_unchecked_hygine_hack_F,[4]).

test(realworld_moveit_gen_3, [fail]) :-
        length(Stmts, 7),
        ctx_pinning(Stmts, _Op, pinned_moved),
        validate_liveness(Stmts).

test(realworld_moveit_gen_4, [nondet]) :-
        length(Stmts, 8),
        ctx_pinning(Stmts, _Op, pinned_moved),
        validate_liveness(Stmts).

:- end_tests(realworld_moveit).
