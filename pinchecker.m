%---------------------------------------------------------------------------%
%
% File: pinchecker.m
% Version: 0.0.1
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>
%
% This module provides an compilable implementation of PinChecker.
%
%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- module pinchecker.
:- interface.

:- import_module io.

%---------------------------------------------------------------------------%

:- pred main(io::di, io::uo) is det.

%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- implementation.

:- import_module list.
:- import_module require.
:- import_module string.

:- type rs_func
    --->    move_F
    ;       unmovable_new_F.

:- type rs_type
    --->    unmovable_T.

:- type rs_stmt
    --->    rs_stmt(
                line    :: int,
                fn      :: rs_func,
                args    :: list(int)
            ).

%---------------------------------------------------------------------------%

main(!IO) :-
    Stmts = [rs_stmt(2, move_F, [1]),
             rs_stmt(1, unmovable_new_F, [])],
    debug_rs_stmts(Stmts, Repr),
    io.format("%s\n", [s(Repr)], !IO).

:- pred fn_typing(rs_func, list(rs_type), rs_type).
:- mode fn_typing(in, in, out) is semidet.
:- mode fn_typing(in, out, in) is semidet.

fn_typing(move_F, [T], T).
fn_typing(unmovable_new_F, [], unmovable_T).

%---------------------------------------------------------------------------%
%
% Convert rs_* structures to string representations for debugging purposes.
%

:- pred debug_rs_func(rs_func::in, string::out) is det.

debug_rs_func(Func, Repr) :-
    ( Func = move_F ->
        Repr = "move_F"
    ; Func = unmovable_new_F ->
        Repr = "unmovable_new_F"
    ;
        unexpected($pred, "unknown Func")
    ).

:- pred debug_rs_stmt(rs_stmt::in, string::out) is det.

debug_rs_stmt(Stmt, Repr) :-
    Stmt = rs_stmt(Line, Func, Args),
    debug_rs_func(Func, FuncRepr),
    list.map(int_to_string, Args, ArgStrs),
    ArgsRepr = string.join_list(",", ArgStrs),
    string.format("rs_stmt(%d,%s,[%s])", 
                  [i(Line), s(FuncRepr), s(ArgsRepr)], 
                  Repr).

:- pred debug_rs_stmts(list(rs_stmt)::in, string::out) is det.

debug_rs_stmts(Stmts, Repr) :-
    list.map(debug_rs_stmt, Stmts, Reprs),
    Repr = string.join_list("\n", Reprs).

%---------------------------------------------------------------------------%
:- end_module pinchecker.
%---------------------------------------------------------------------------%
