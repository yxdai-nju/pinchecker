%---------------------------------------------------------------------------%
%
% File: pinchecker_test.m
% Version: 0.1.0
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>
%
% This module provides tests for `pinchecker' module.
%
%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- module pinchecker_test.
:- interface.

:- import_module io.

%---------------------------------------------------------------------------%

:- pred main(io::di, io::uo) is det.

%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- implementation.

:- import_module list.
:- import_module solutions.
:- import_module string.

:- import_module pinchecker.

%---------------------------------------------------------------------------%

main(!IO) :-
    test_1(!IO),
    test_2(!IO).

%---------------------------------------------------------------------------%

:- type rs_func
    --->    move_F
    ;       borrow_F
    ;       borrow_mut_F
    ;       store_new_F
    ;       store_two_new_F
    ;       unmovable_new_F.

:- type rs_type
    --->    ref_T(rs_type)
    ;       mutref_T(rs_type)
    ;       store_T(rs_type)
    ;       store_two_T(rs_type, rs_type)
    ;       unmovable_T.

:- type rs_trait
    --->    copy_Tr
    ;       deref_Tr(rs_type)
    ;       derefmut_Tr(rs_type).

:- instance rust_tc(rs_func, rs_type, rs_trait) where [
    func(fn_rpil_tcm/1) is fn_rpil,
    pred(does_not_kill_arguments_tcm/1) is does_not_kill_arguments,
    pred(fn_typing_tcm/3) is fn_typing,
    pred(lives_even_after_killing_tcm/1) is lives_even_after_killing,
    pred(impl_trait_tcm/2) is impl_trait
].

:- instance showable(rs_func) where [
    func(show/1) is show_rs_func
].

:- pred fn_typing(rs_func, list(rs_type), rs_type).
:- mode fn_typing(in, in, out) is semidet.
:- mode fn_typing(out, out, in) is multi.

:- func fn_rpil(rs_func) = list(rpil_inst).

:- pred impl_trait(rs_type, rs_trait).
:- mode impl_trait(in, in) is semidet.

:- pred lives_even_after_killing(rs_type).
:- mode lives_even_after_killing(in) is semidet.

:- pred does_not_kill_arguments(rs_func).
:- mode does_not_kill_arguments(in) is semidet.

:- func show_rs_func(rs_func) = string.

%---------------------------------------------------------------------------%
%
% Volatile
%

fn_typing(move_F, [T], T).
fn_typing(borrow_F, [T], ref_T(T)).
fn_typing(borrow_mut_F, [T], mutref_T(T)).
fn_typing(store_new_F, [T], store_T(T)).
fn_typing(store_two_new_F, [T1, T2], store_two_T(T1, T2)).
fn_typing(unmovable_new_F, [], unmovable_T).

fn_rpil(move_F) =
    [ rpil_bind(arg(0), arg(1))
    , rpil_move(arg(1))
    ].
fn_rpil(borrow_F) =
    [ rpil_borrow(arg(0), arg(1))
    ].
fn_rpil(borrow_mut_F) =
    [ rpil_borrow_mut(arg(0), arg(1))
    ].
fn_rpil(store_new_F) =
    [ rpil_bind(place(arg(0),1), arg(1))
    , rpil_move(arg(1))
    ].
fn_rpil(store_two_new_F) =
    [ rpil_bind(place(arg(0),1), arg(1))
    , rpil_bind(place(arg(0),2), arg(2))
    , rpil_move(arg(1))
    , rpil_move(arg(2))
    ].
fn_rpil(unmovable_new_F) =
    [ ].

impl_trait(ref_T(_), copy_Tr).
impl_trait(ref_T(T), deref_Tr(T)).
impl_trait(mutref_T(T), derefmut_Tr(T)).

lives_even_after_killing(mutref_T(_)).
lives_even_after_killing(Type) :-
    impl_trait(Type, copy_Tr).

does_not_kill_arguments(Fn) :-
    (
        Fn = borrow_F
    ;
        Fn = borrow_mut_F
    ).

show_rs_func(move_F) = "move".
show_rs_func(borrow_F) = "&".
show_rs_func(borrow_mut_F) = "&mut ".
show_rs_func(store_new_F) = "Store::new".
show_rs_func(store_two_new_F) = "StoreTwo::new".
show_rs_func(unmovable_new_F) = "Unmovable::new".

%---------------------------------------------------------------------------%

:- pred test_1(io::di, io::uo) is det.

:- pred test_2(io::di, io::uo) is det.

:- func show_rs_type(rs_type) = string.

%---------------------------------------------------------------------------%

test_1(!IO) :-
    TestStmts = [
        rs_stmt(4, move_F, [3]),
        rs_stmt(3, store_new_F, [2]),
        rs_stmt(2, borrow_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    io.print_line(show_rs_stmts(TestStmts), !IO),
    ( ctx_borrowing(TestStmts, place(var(4),1), var(1), shared) ->
        io.print("succeeds\n", !IO)
    ;
        io.print("failed\n", !IO)
    ).

test_2(!IO):-
    StmtsUninit = uninit_stmts(4),
    solutions(
        (pred(Stmts::out) is nondet :-
            Type = store_T(ref_T(unmovable_T)),
            ctx_typing_gen(StmtsUninit, Stmts, 4, Type),
            ctx_borrowing(Stmts, place(var(4),1), var(1), shared)
        ),
        Solutions
    ),
    Reprs = list.map(show_rs_stmts, Solutions),
    Sep = "\n--------------------------------\n",
    Repr = string.join_list(Sep, Reprs),
    io.format("%s\n", [s(Repr)], !IO).

%---------------------%

show_rs_type(ref_T(T)) =
    string.format("&%s", [s(TR)]) :-
    TR = show_rs_type(T).
show_rs_type(mutref_T(T)) =
    string.format("&mut %s", [s(TR)]) :-
    TR = show_rs_type(T).
show_rs_type(store_T(T)) =
    string.format("Store<%s>", [s(TR)]) :-
    TR = show_rs_type(T).
show_rs_type(store_two_T(T1, T2)) =
    string.format("StoreTwo<%s, %s>", [s(T1R), s(T2R)]) :-
    T1R = show_rs_type(T1),
    T2R = show_rs_type(T2).
show_rs_type(unmovable_T) = "Unmovable".

%---------------------------------------------------------------------------%
:- end_module pinchecker_test.
%---------------------------------------------------------------------------%
