%---------------------------------------------------------------------------%
%
% File: pinchecker_test.m
% Version: 0.1.5
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
:- import_module set.
:- import_module solutions.
:- import_module string.
:- import_module unit.

:- import_module pinchecker.

%---------------------------------------------------------------------------%

main(!IO) :-
    run_test(test_ctx_typing_1, "ctx_typing_1", !IO),
    run_test_fails(test_ctx_typing_2_fail, "ctx_typing_2", !IO),
    run_test_fails(test_ctx_typing_3_fail, "ctx_typing_3", !IO),
    run_test(test_ctx_typing_4, "ctx_typing_4", !IO),
    run_test_fails(test_ctx_typing_5_fail, "ctx_typing_5", !IO),
    run_test(test_ctx_typing_trait_1, "ctx_typing_trait_1", !IO),
    run_test(test_lives_even_after_killing_1, "lives_even_after_killing_1", !IO),
    run_test(test_lives_even_after_killing_2, "lives_even_after_killing_2", !IO),
    run_test_fails(test_lives_even_after_killing_3_fail, "lives_even_after_killing_3", !IO),
    run_test(test_ctx_liveness_1, "ctx_liveness_1", !IO),
    run_test_fails(test_ctx_liveness_2_fail, "ctx_liveness_2", !IO),
    run_test(test_ctx_places_1, "ctx_places_1", !IO),
    run_test(test_ctx_borrowing_1, "ctx_borrowing_1", !IO),
    run_test(test_ctx_borrowing_2, "ctx_borrowing_2", !IO),
    run_test_fails(test_ctx_borrowing_liveness_1_fail, "ctx_borrowing_liveness_1", !IO),
    run_test(test_ctx_borrowing_liveness_2, "ctx_borrowing_liveness_2", !IO),
    run_test_fails(test_ctx_borrowing_liveness_3_fail, "ctx_borrowing_liveness_3", !IO),
    run_test(test_ctx_pinning_1, "ctx_pinning_1", !IO),
    run_test(test_ctx_pinning_2, "ctx_pinning_2", !IO),
    run_test(test_ctx_pinning_3, "ctx_pinning_3", !IO),
    run_test(test_ctx_pinning_4, "ctx_pinning_4", !IO),
    run_test(test_ctx_pinning_5, "ctx_pinning_5", !IO),
    run_test(test_ctx_pinning_6, "ctx_pinning_6", !IO),
    run_test(test_gen_1, "gen_1", !IO).

%---------------------------------------------------------------------------%

:- instance rust_tc(rs_func, rs_type, rs_trait) where [
    func(fn_rpil_tcm/1) is fn_rpil,
    pred(does_not_kill_arguments_tcm/1) is does_not_kill_arguments,
    pred(fn_typing_tcm/3) is fn_typing,
    pred(type_compatible_tcm/2) is type_compatible,
    pred(lives_even_after_killing_tcm/1) is lives_even_after_killing,
    pred(impl_trait_tcm/2) is impl_trait
].

:- instance showable(rs_func) where [
    func(show/1) is show_rs_func
].

:- func fn_rpil(rs_func) = list(rpil_inst).

:- pred does_not_kill_arguments(rs_func).
:- mode does_not_kill_arguments(in) is semidet.

:- pred fn_typing(rs_func, list(rs_type), rs_type).
:- mode fn_typing(in, in, out) is nondet.
:- mode fn_typing(out, out, in) is multi.

:- pred type_compatible(rs_type, rs_type).
:- mode type_compatible(in, out) is multi.

:- pred lives_even_after_killing(rs_type).
:- mode lives_even_after_killing(in) is semidet.

:- pred impl_trait(rs_type, rs_trait).
:- mode impl_trait(in, out) is nondet.

:- func show_rs_func(rs_func) = string.

%---------------------------------------------------------------------------%
%
% Volatile
%

:- type rs_func
    --->    move_F
    ;       borrow_F
    ;       borrow_mut_F
    ;       option_some_F
    ;       option_none_F
    ;       store_new_F
    ;       store_two_new_F
    ;       unmovable_new_F
    ;       pin_new_unchecked_F
    ;       borrow_mut_option_p1_F
    ;       pin_and_move_F
    ;       pin_macro_F.

show_rs_func(move_F) = "move".
show_rs_func(borrow_F) = "&".
show_rs_func(borrow_mut_F) = "&mut ".
show_rs_func(option_some_F) = "Option::Some".
show_rs_func(option_none_F) = "Option::None".
show_rs_func(store_new_F) = "Store::new".
show_rs_func(store_two_new_F) = "StoreTwo::new".
show_rs_func(unmovable_new_F) = "Unmovable::new".
show_rs_func(pin_new_unchecked_F) = "Pin::new_unchecked".
show_rs_func(borrow_mut_option_p1_F) = "borrow_mut_option_p1".
show_rs_func(pin_and_move_F) = "pin_and_move".
show_rs_func(pin_macro_F) = "pin!".

:- type rs_type
    --->    ref_T(rs_type)
    ;       mutref_T(rs_type)
    ;       option_T(rs_type)
    ;       pin_T(rs_type)
    ;       store_T(rs_type)
    ;       store_two_T(rs_type, rs_type)
    ;       unmovable_T
    ;       unit_T
    ;       free_type.

type_compatible(free_type, free_type).
type_compatible(CompType, Type) :-
    (
        Type = CompType
    ;
        (
            CompType = ref_T(CT1),
            type_compatible(CT1, T1),
            Type = ref_T(T1)
        ;
            CompType = mutref_T(CT1),
            type_compatible(CT1, T1),
            Type = mutref_T(T1)
        ;
            CompType = option_T(CT1),
            type_compatible(CT1, T1),
            Type = option_T(T1)
        ;
            CompType = pin_T(CT1),
            type_compatible(CT1, T1),
            Type = pin_T(T1)
        ;
            CompType = store_T(CT1),
            type_compatible(CT1, T1),
            Type = store_T(T1)
        ;
            CompType = store_two_T(CT1, CT2),
            type_compatible(CT1, T1),
            type_compatible(CT2, T2),
            Type = store_two_T(T1, T2)
        )
    ;
        Type = free_type
    ).

fn_typing(move_F, [T], T).
fn_typing(borrow_F, [T], ref_T(T)).
fn_typing(borrow_mut_F, [T], mutref_T(T)).
fn_typing(option_some_F, [T], option_T(T)).
fn_typing(option_none_F, [], option_T(free_type)).
fn_typing(store_new_F, [T], store_T(T)).
fn_typing(store_two_new_F, [T1, T2], store_two_T(T1, T2)).
fn_typing(unmovable_new_F, [], unmovable_T).
fn_typing(pin_new_unchecked_F, [Ptr], pin_T(Ptr)) :-
    impl_trait(Ptr, deref_Tr(_)).
fn_typing(borrow_mut_option_p1_F, [mutref_T(option_T(T))], mutref_T(T)).
fn_typing(pin_and_move_F, [free_type], unit_T).
fn_typing(pin_macro_F, [T], pin_T(mutref_T(T))).

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
fn_rpil(option_some_F) =
    [ rpil_bind(place(arg(0),1), arg(1))
    , rpil_move(arg(1))
    ].
fn_rpil(option_none_F) =
    [ ].
fn_rpil(store_new_F) =
    [ rpil_bind(place(arg(0),1), arg(1))
    , rpil_move(arg(1))
    ].
fn_rpil(store_two_new_F) =
    [ rpil_bind(place(arg(0),2), arg(2))
    , rpil_move(arg(2))
    , rpil_bind(place(arg(0),1), arg(1))
    , rpil_move(arg(1))
    ].
fn_rpil(unmovable_new_F) =
    [ ].
fn_rpil(pin_new_unchecked_F) =
    [ rpil_bind(arg(0), arg(1))
    , rpil_deref_pin(arg(1))
    ].
fn_rpil(borrow_mut_option_p1_F) =
    [ rpil_borrow_mut(arg(0), place(deref(arg(1)),1))
    ].
fn_rpil(pin_and_move_F) =
    [ rpil_deref_move(arg(1))
    , rpil_deref_pin(arg(1))
    ].
fn_rpil(pin_macro_F) =
    [ rpil_deref_pin(arg(0))
    , rpil_borrow_mut(arg(0), place_ext(arg(0)))
    , rpil_move(arg(1))
    ].

:- type rs_trait
    --->    copy_Tr
    ;       deref_Tr(rs_type)
    ;       derefmut_Tr(rs_type).

impl_trait(ref_T(_), copy_Tr).
impl_trait(option_T(T), copy_Tr) :-
    impl_trait(T, copy_Tr).
impl_trait(ref_T(T), deref_Tr(T)).
impl_trait(mutref_T(T), deref_Tr(T)).
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

%---------------------------------------------------------------------------%

:- pred test_ctx_typing_1(unit::in) is semidet.
:- pred test_ctx_typing_2_fail(unit::in) is semidet.
:- pred test_ctx_typing_3_fail(unit::in) is semidet.
:- pred test_ctx_typing_4(unit::in) is semidet.
:- pred test_ctx_typing_5_fail(unit::in) is semidet.
:- pred test_ctx_typing_trait_1(unit::in) is semidet.
:- pred test_lives_even_after_killing_1(unit::in) is semidet.
:- pred test_lives_even_after_killing_2(unit::in) is semidet.
:- pred test_lives_even_after_killing_3_fail(unit::in) is semidet.
:- pred test_ctx_liveness_1(unit::in) is semidet.
:- pred test_ctx_liveness_2_fail(unit::in) is semidet.
:- pred test_ctx_places_1(unit::in) is semidet.
:- pred test_ctx_borrowing_1(unit::in) is semidet.
:- pred test_ctx_borrowing_2(unit::in) is semidet.
:- pred test_ctx_borrowing_liveness_1_fail(unit::in) is semidet.
:- pred test_ctx_borrowing_liveness_2(unit::in) is semidet.
:- pred test_ctx_borrowing_liveness_3_fail(unit::in) is semidet.
:- pred test_ctx_pinning_1(unit::in) is semidet.
:- pred test_ctx_pinning_2(unit::in) is semidet.
:- pred test_ctx_pinning_3(unit::in) is semidet.
:- pred test_ctx_pinning_4(unit::in) is semidet.
:- pred test_ctx_pinning_5(unit::in) is semidet.
:- pred test_ctx_pinning_6(unit::in) is semidet.
:- pred test_gen_1(unit::in) is semidet.

%---------------------%

:- pred run_test(pred(unit), string, io, io).
:- mode run_test(pred(in) is semidet, in, di, uo) is det.

:- pred run_test_fails(pred(unit), string, io, io).
:- mode run_test_fails(pred(in) is semidet, in, di, uo) is det.

%---------------------------------------------------------------------------%

test_ctx_typing_1(_) :-
    Stmts = [
        rs_stmt(2, store_new_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_typing(Stmts, 2, store_T(unmovable_T)).

% TODO: fix bugs to make this case pass
test_ctx_typing_2_fail(_) :-
    Stmts = [
        rs_stmt(2, store_two_new_F, [1, 1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_typing(Stmts, 2, _Type).

% TODO: fix bugs to make this case pass
test_ctx_typing_3_fail(_) :-
    Stmts = [
        rs_stmt(3, store_two_new_F, [1, 2]),
        rs_stmt(2, borrow_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_typing(Stmts, 3, _Type).

test_ctx_typing_4(_) :-
    Stmts = [
        rs_stmt(3, pin_and_move_F, [2]),
        rs_stmt(2, borrow_mut_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_typing(Stmts, 3, unit_T).

test_ctx_typing_5_fail(_) :-
    Stmts = [
        rs_stmt(3, borrow_F, [1]),
        rs_stmt(2, move_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_typing(Stmts, 3, _Type).

test_ctx_typing_trait_1(_) :-
    Stmts = [
        rs_stmt(3, pin_new_unchecked_F, [2]),
        rs_stmt(2, borrow_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_typing(Stmts, 3, pin_T(ref_T(unmovable_T))),
    ctx_typing(Stmts, 2, ref_T(unmovable_T)),
    ctx_typing(Stmts, 1, unmovable_T).

test_lives_even_after_killing_1(_) :-
    lives_even_after_killing(mutref_T(unmovable_T)).

test_lives_even_after_killing_2(_) :-
    lives_even_after_killing(option_T(ref_T(unmovable_T))).

test_lives_even_after_killing_3_fail(_) :-
    lives_even_after_killing(option_T(mutref_T(unmovable_T))).

test_ctx_liveness_1(_) :-
    Stmts = [
        rs_stmt(3, move_F, [1]),
        rs_stmt(2, borrow_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_liveness(Stmts, 2, dead).

test_ctx_liveness_2_fail(_) :-
    Stmts = [
        rs_stmt(1, borrow_F, [1])
    ],
    ctx_liveness(Stmts, 1, _Liveness).

test_ctx_places_1(_) :-
    Stmts = [
        rs_stmt(2, pin_macro_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    Places = ctx_places(Stmts, 2),
    ExpectedPlaces = list_to_set([var(2), place_ext(var(2))]),
    set.equal(ExpectedPlaces, Places).

test_ctx_borrowing_1(_) :-
    Stmts = [
        rs_stmt(4, move_F, [3]),
        rs_stmt(3, store_new_F, [2]),
        rs_stmt(2, borrow_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_borrowing(Stmts, place(var(4),1), var(1), shared).

test_ctx_borrowing_2(_) :-
    Stmts = [
        rs_stmt(4, borrow_mut_option_p1_F, [3]),
        rs_stmt(3, borrow_mut_F, [2]),
        rs_stmt(2, option_some_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_borrowing(Stmts, var(4), place(var(2),1), mutable),
    ctx_borrowing(Stmts, var(3), var(2), mutable).

test_ctx_borrowing_liveness_1_fail(_) :-
    Stmts = [
        rs_stmt(3, move_F, [1]),
        rs_stmt(2, borrow_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_borrowing(Stmts, var(2), var(1), shared).

test_ctx_borrowing_liveness_2(_) :-
    Stmts = [
        rs_stmt(5, store_new_F, [4]),
        rs_stmt(4, borrow_mut_option_p1_F, [3]),
        rs_stmt(3, borrow_mut_F, [2]),
        rs_stmt(2, option_some_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_borrowing(Stmts, place(var(5),1), place(var(2),1), mutable),
    ctx_borrowing(Stmts, var(4), place(var(2),1), mutable).

test_ctx_borrowing_liveness_3_fail(_) :-
    Stmts = [
        rs_stmt(6, move_F, [2]),
        rs_stmt(5, store_new_F, [4]),
        rs_stmt(4, borrow_mut_option_p1_F, [3]),
        rs_stmt(3, borrow_mut_F, [2]),
        rs_stmt(2, option_some_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_borrowing(Stmts, place(var(5),1), place(var(2),1), mutable).

test_ctx_pinning_1(_) :-
    Stmts = [
        rs_stmt(3, pin_new_unchecked_F, [2]),
        rs_stmt(2, borrow_mut_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_pinning(Stmts, var(1), pinned).

test_ctx_pinning_2(_) :-
    Stmts = [
        rs_stmt(4, move_F, [1]),
        rs_stmt(3, pin_new_unchecked_F, [2]),
        rs_stmt(2, borrow_mut_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_pinning(Stmts, var(1), moved).

test_ctx_pinning_3(_) :-
    Stmts = [
        rs_stmt(5, pin_new_unchecked_F, [4]),
        rs_stmt(4, borrow_mut_F, [1]),
        rs_stmt(3, option_some_F, [2]),
        rs_stmt(2, unmovable_new_F, []),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_pinning(Stmts, var(1), pinned).

test_ctx_pinning_4(_) :-
    Stmts = [
        rs_stmt(8, pin_new_unchecked_F, [6]),
        rs_stmt(7, pin_new_unchecked_F, [4]),
        rs_stmt(6, borrow_mut_option_p1_F, [5]),
        rs_stmt(5, borrow_mut_F, [3]),
        rs_stmt(4, borrow_mut_F, [1]),
        rs_stmt(3, option_some_F, [2]),
        rs_stmt(2, unmovable_new_F, []),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_pinning(Stmts, place(var(3),1), pinned),
    ctx_pinning(Stmts, var(1), pinned).

test_ctx_pinning_5(_) :-
    Stmts = [
        rs_stmt(3, pin_and_move_F, [2]),
        rs_stmt(2, borrow_mut_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_pinning(Stmts, var(1), moved).

test_ctx_pinning_6(_) :-
    Stmts = [
        rs_stmt(3, move_F, [2]),
        rs_stmt(2, pin_macro_F, [1]),
        rs_stmt(1, unmovable_new_F, [])
    ],
    ctx_pinning(Stmts, place_ext(var(2)), pinned).

test_gen_1(_) :-
    FreeStmts = free_stmts(4),
    solutions(
        (pred(Stmts::out) is nondet :-
            Type = store_T(ref_T(unmovable_T)),
            ctx_typing_gen(FreeStmts, Stmts, 4, Type),
            ctx_borrowing(Stmts, place(var(4),1), var(1), shared)
        ),
        Solutions
    ),
    ExpectedSolutions = [
        [rs_stmt(4, move_F, [3]), rs_stmt(3, store_new_F, [2]), rs_stmt(2, borrow_F, [1]), rs_stmt(1, unmovable_new_F, [])],
        [rs_stmt(4, store_new_F, [2]), rs_stmt_free(3), rs_stmt(2, borrow_F, [1]), rs_stmt(1, unmovable_new_F, [])],
        [rs_stmt(4, store_new_F, [3]), rs_stmt(3, move_F, [2]), rs_stmt(2, borrow_F, [1]), rs_stmt(1, unmovable_new_F, [])],
        [rs_stmt(4, store_new_F, [3]), rs_stmt(3, borrow_F, [1]), rs_stmt_free(2), rs_stmt(1, unmovable_new_F, [])]
    ],
    set.equal(list_to_set(Solutions), list_to_set(ExpectedSolutions)).

%---------------------%

run_test(Pred, Name, !IO) :-
    ( call(Pred, unit) ->
        io.format("%%\ttest %s: succeeded\n", [s(Name)], !IO)
    ;
        io.format("!\ttest %s: failed\n", [s(Name)], !IO)
    ).

run_test_fails(Pred, Name, !IO) :-
    ( call(Pred, unit) ->
        io.format("!\ttest %s: failed\n", [s(Name)], !IO)
    ;
        io.format("%%\ttest %s: succeeded\n", [s(Name)], !IO)
    ).

%---------------------------------------------------------------------------%
:- end_module pinchecker_test.
%---------------------------------------------------------------------------%
