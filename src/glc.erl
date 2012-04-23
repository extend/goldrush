%% Copyright (c) 2012, Magnus Klaar <klaar@ninenines.eu>
%%
%% Permission to use, copy, modify, and/or distribute this software for any
%% purpose with or without fee is hereby granted, provided that the above
%% copyright notice and this permission notice appear in all copies.
%%
%% THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
%% WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
%% MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
%% ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
%% WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
%% ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
%% OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.


%% @doc Event filter implementation.
%%
%% An event query is constructed using the built in operators exported from
%% this module. The filtering operators are used to specify which events
%% should be included in the output of the query. The default output action
%% is to copy all events matching the input filters associated with a query
%% to the output. This makes it possible to construct and compose multiple
%% queries at runtime.
%%
%% === Examples of built in filters ===
%% ```
%% %% Select all events where 'a' exists and is greater than 0.
%% glc:gt(a, 0).
%% %% Select all events where 'a' exists and is equal to 0.
%% glc:eq(a, 0).
%% %% Select all events where 'a' exists and is less than 0.
%% glc:lt(a, 0).
%%
%% %% Select no input events. Used as black hole query.
%% glc:null(false).
%% %% Select all input events. Used as passthrough query.
%% glc:null(true).
%% '''
%%
%% === Examples of combining filters ===
%% ```
%% %% Select all events where both 'a' and 'b' exists and are greater than 0.
%% glc:all([glc:gt(a, 0), glc:gt(b, 0)]).
%% %% Select all events where 'a' or 'b' exists and are greater than 0.
%% glc:any([glc:get(a, 0), glc:gt(b, 0)]).
%% '''
%%
%% === Handling output events ===
%%
%% Once a query has been composed it is possible to override the output action
%% with an erlang function. The function will be applied to each output event
%% from the query. The return value from the function will be ignored.
%%
%% ```
%% %% Write all input events as info reports to the error logger.
%% glc:with(glc:null(true), fun(E) ->
%%     error_logger:info_report(gre:pairs(E)) end).
%% '''
%%
-module(glc).

-export([
    compile/2,
    handle/2,
    delete/1
]).

-export([
    lt/2,
    eq/2,
    gt/2
]).

-export([
    all/1,
    any/1,
    null/1,
    with/2
]).

-record(module, {
    'query' :: term(),
    tables :: [{atom(), ets:tid()}],
    qtree :: term()
}).

-type syntaxTree() :: erl_syntax:syntaxTree().

-record(state, {
    event = undefined :: syntaxTree(),
    fields = [] :: [{atom(), syntaxTree()}],
    fieldc = 0 :: non_neg_integer(),
    paramvars = [] :: [{term(), syntaxTree()}],
    paramstab = undefined :: ets:tid()
}).

-type nextFun() :: fun((#state{}) -> [syntaxTree()]).
-type q() :: tuple().

-spec lt(atom(), term()) -> q().
lt(Key, Term) when is_atom(Key) -> {Key, '<', Term}.

-spec eq(atom(), term()) -> q().
eq(Key, Term) when is_atom(Key) -> {Key, '=', Term}.

-spec gt(atom(), term()) -> q().
gt(Key, Term) when is_atom(Key) -> {Key, '>', Term}.


%% @doc Apply multiple conditions to the input.
%% For an event to be considered valid output the condition of all filters
%% specified in the input must hold for the input event.
-spec all([q()]) -> q().
all(Conds) when is_list(Conds) ->
    {all, Conds}.

%% @doc Apply one of multiple conditions to the input.
-spec any([q()]) -> q().
any(Conds) when is_list(Conds) ->
    {any, Conds}.

%% @doc Always return `true' or `false'.
-spec null(boolean()) -> q().
null(Result) when is_boolean(Result) ->
    {null, Result}.

%% @doc Apply a function to each output.
-spec with(q(), fun((gre:event()) -> term())) -> q().
with(Query, Fun) when is_function(Fun, 1) ->
    {with, Query, Fun}.


%% @doc Compile a query to a module.
%%
%% On success the module representing the query is returned. The module and
%% data associated with the query must be released using the {@link delete/1}
%% function. The name of the query module is expected to be unique.
-spec compile(atom(), list()) -> {ok, atom()}.
compile(Module, Query) ->
    {ok, ModuleData} = module_data(Query),
    {ok, forms, Forms} = abstract_module(Module, ModuleData),
    {ok, Module, Binary} = compile_forms(Forms, []),
    {ok, loaded, Module} = load_binary(Module, Binary),
    {ok, Module}.

%% @doc Handle an event using a compiled query.
%%
%% The input event is expected to have been returned from {@link gre:make/2}.
-spec handle(atom(), gre:event()) -> ok.
handle(Module, Event) ->
    Module:handle(Event).

%% @doc Release a compiled query.
%%
%% This releases all resources allocated by a compiled query. The query name
%% is expected to be associated with an existing query module. Calling this
%% function will result in a runtime error.
-spec delete(atom()) -> ok.
delete(_Module) ->
    ok.


%% @private Map a query to a module data term.
-spec module_data(term()) -> {ok, #module{}}.
module_data(Query) ->
    %% terms in the query which are not valid arguments to the
    %% erl_syntax:abstract/1 functions are stored in ETS.
    %% the terms are only looked up once they are necessary to
    %% continue evaluation of the query.
    Params = ets:new(params, [set,protected]),
    %% query counters are stored in a shared ETS table. this should
    %% be an optional feature. enable by defaults to simplify tests.
    Counters = ets:new(counters, [set,public]),
    ets:insert(Counters, [{input,0}, {filter,0}, {output,0}]),
    %% the abstract_tables/1 function expects a list of name-tid pairs.
    %% tables are referred to by name in the generated code. the table/1
    %% function maps names to tids.
    Tables = [{params,Params}, {counters,Counters}],
    Tree = query_tree(Query),
    {ok, #module{'query'=Query, tables=Tables, qtree=Tree}}.


%% @private Map a query to a simplified query tree term.
%%
%% The simplified query tree is used to combine multiple queries into one
%% query module. The goal of this is to reduce the filtering and dispatch
%% overhead when multiple concurrent queries are executed.
%%
%% A fixed selection condition may be used to specify a property that an event
%% must have in order to be considered part of the input stream for a query.
%%
%% For the sake of simplicity it is only possible to define selection
%% conditions using the fields present in the context and identifiers
%% of an event. The fields in the context are bound to the reserved
%% names:
%%
%% - '$n': node name
%% - '$a': application name
%% - '$p': process identifier
%% - '$t': timestamp
%% 
%%
%% If an event must be selected based on the runtime state of an event handler
%% this must be done in the body of the handler.
-type qcond() ::
    {atom(), '<', term()} |
    {atom(), '=', term()} |
    {atom(), '>', term()} |
    {any, [qcond()]} |
    {all, [qcond()]}.
-type qbody() :: tuple().
-type qtree() :: [{qcond(), qbody()}].
-spec query_tree(term()) -> qtree().
query_tree(Query) ->
    Query.

%% abstract code geneation functions

%% @private Generate an abstract dispatch module.
-spec abstract_module(atom(), #module{}) -> {ok, forms, list()}.
abstract_module(Module, Data) ->
    Forms = [erl_syntax:revert(E) || E <- abstract_module_(Module, Data)],
    case lists:keyfind(errors, 1, erl_syntax_lib:analyze_forms(Forms)) of
        false -> {ok, forms, Forms};
        {_, []} -> {ok, forms, Forms};
        {_, [_|_]}=Errors -> Errors
    end.

%% @private Generate an abstract dispatch module.
-spec abstract_module_(atom(), #module{}) -> [erl_syntax:syntaxTree()].
abstract_module_(Module, #module{tables=Tables, qtree=Tree}=Data) ->
    {_, ParamsTable} = lists:keyfind(params, 1, Tables),
    AbstractMod = [
     %% -module(Module)
     erl_syntax:attribute(erl_syntax:atom(module), [erl_syntax:atom(Module)]),
     %% -export([
     erl_syntax:attribute(
       erl_syntax:atom(export),
       [erl_syntax:list([
        %% info/1
        erl_syntax:arity_qualifier(
            erl_syntax:atom(info),
            erl_syntax:integer(1)),
        %% table/1
        erl_syntax:arity_qualifier(
            erl_syntax:atom(table),
            erl_syntax:integer(1)),
        %% handle/1
        erl_syntax:arity_qualifier(
            erl_syntax:atom(handle),
            erl_syntax:integer(1))])]),
     %% ]).
     %% info(Name) -> Term.
     erl_syntax:function(
        erl_syntax:atom(info),
        abstract_info(Data) ++
        [erl_syntax:clause(
            [erl_syntax:underscore()], none,
                [erl_syntax:application(
                 erl_syntax:atom(erlang),
                 erl_syntax:atom(error),
                 [erl_syntax:atom(badarg)])])]),
     %% table(Name) -> ets:tid().
     erl_syntax:function(
        erl_syntax:atom(table),
        abstract_tables(Tables) ++
        [erl_syntax:clause(
         [erl_syntax:underscore()], none,
            [erl_syntax:application(
             erl_syntax:atom(erlang),
             erl_syntax:atom(error),
             [erl_syntax:atom(badarg)])])]),
     %% handle(Event) - entry function
     erl_syntax:function(
       erl_syntax:atom(handle),
       [erl_syntax:clause([erl_syntax:variable("Event")], none,
         [abstract_count(input),
          erl_syntax:application(none,
            erl_syntax:atom(handle_), [erl_syntax:variable("Event")])])]),
     %% input_(Node, App, Pid, Tags, Values) - filter roots
     erl_syntax:function(
        erl_syntax:atom(handle_),
        [erl_syntax:clause([erl_syntax:variable("Event")], none,
         abstract_filter(Tree, #state{
            event=erl_syntax:variable("Event"),
            paramstab=ParamsTable}))])
    ],
    %% Transform Term -> Key to Key -> Term
    ParamsList = [{K, V} || {V, K} <- ets:tab2list(ParamsTable)],
    ets:delete_all_objects(ParamsTable),
    ets:insert(ParamsTable, ParamsList),
    AbstractMod.

%% @private Return the clauses of the table/1 function.
abstract_tables(Tables) ->
    [erl_syntax:clause(
        [erl_syntax:abstract(K)], none,
        [erl_syntax:abstract(V)])
    || {K, V} <- Tables].

%% @private Return the clauses of the info/1 function.
abstract_info(#module{'query'=Query}) ->
    [erl_syntax:clause([erl_syntax:abstract(K)], none, V)
        || {K, V} <- [
        {'query', abstract_query(Query)},
        {input, abstract_getcount(input)},
        {filter, abstract_getcount(filter)},
        {output, abstract_getcount(output)}
    ]].

%% @private Return the original query as an expression.
abstract_query({with, _, _}) ->
    [erl_syntax:abstract([])];
abstract_query(Query) ->
    [erl_syntax:abstract(Query)].


%% @private Return a list of expressions to apply a filter.
%% @todo Allow mulitple functions to be specified using `with/2'.
-spec abstract_filter(q(), #state{}) -> [syntaxTree()].
abstract_filter({with, Cond, Fun}, State) ->
    abstract_filter_(Cond,
        _OnMatch=fun(State2) ->
            [abstract_count(output)] ++ abstract_with(Fun, State2) end,
        _OnNomatch=fun(_State2) -> [abstract_count(filter)] end, State);
abstract_filter(Cond, State) ->
    abstract_filter_(Cond,
        _OnMatch=fun(_State2) -> [abstract_count(output)] end,
        _OnNomatch=fun(_State2) -> [abstract_count(filter)] end, State).

%% @private Return a list of expressions to apply a filter.
%% A filter expects two continuation functions which generates the expressions
%% to apply when the filter matches or fails to match. The state passed to the
%% functions will be contain all variable bindings to previously accessed
%% fields and parameters.
-spec abstract_filter_(qcond(), nextFun(), nextFun(), #state{}) ->
        syntaxTree().
abstract_filter_({null, true}, OnMatch, _OnNomatch, State) ->
    OnMatch(State);
abstract_filter_({null, false}, _OnMatch, OnNomatch, State) ->
    OnNomatch(State);
abstract_filter_({Key, Op, Value}, OnMatch, OnNomatch, State)
        when Op =:= '>'; Op =:= '='; Op =:= '<' ->
    Op2 = case Op of '=' -> '=:='; Op -> Op end,
    abstract_opfilter(Key, Op2, Value, OnMatch, OnNomatch, State);
abstract_filter_({'any', Conds}, OnMatch, OnNomatch, State) ->
    abstract_any(Conds, OnMatch, OnNomatch, State);
abstract_filter_({'all', Conds}, OnMatch, OnNomatch, State) ->
    abstract_all(Conds, OnMatch, OnNomatch, State).

%% @private Return a branch based on a built in operator.
-spec abstract_opfilter(atom(), atom(), term(), nextFun(),
        nextFun(), #state{}) -> [syntaxTree()].
abstract_opfilter(Key, Opname, Value, OnMatch, OnNomatch, State) ->
    abstract_getkey(Key,
        _OnMatch=fun(#state{fields=Fields}=State2) ->
            {_, Field} = lists:keyfind(Key, 1, Fields),
            [erl_syntax:case_expr(
                erl_syntax:application(
                    erl_syntax:atom(erlang), erl_syntax:atom(Opname),
                    [Field, erl_syntax:abstract(Value)]),
                [erl_syntax:clause([erl_syntax:atom(true)], none, 
                    OnMatch(State2)),
                 erl_syntax:clause([erl_syntax:atom(false)], none,
                    OnNomatch(State2))])] end,
        _OnNomatch=fun(State2) -> OnNomatch(State2) end, State).


%% @private Generate an `all' filter.
%% An `all' filter is evaluated by testing all conditions that must hold. If
%% any of the conditions does not hold the evaluation is short circuted at that
%% point. This means that the `OnNomatch' branch is executed once for each
%% condition. The `OnMatch' branch is only executed once.
-spec abstract_all([qcond()], nextFun(), nextFun(), #state{}) ->
        [syntaxTree()].
abstract_all([H|T], OnMatch, OnNomatch, State) ->
    abstract_filter_(H,
        _OnMatch=fun(State2) -> abstract_all(T, OnMatch, OnNomatch, State2)
            end, OnNomatch, State);
abstract_all([], OnMatch, _OnNomatch, State) ->
    OnMatch(State).

%% @private
-spec abstract_any([qcond()], nextFun(), nextFun(), #state{}) ->
        [syntaxTree()].
abstract_any([H|T], OnMatch, OnNomatch, State) ->
    abstract_filter_(H, OnMatch,
        _OnNomatch=fun(State2) -> abstract_any(T, OnMatch, OnNomatch, State2)
        end, State);
abstract_any([], _OnMatch, OnNomatch, State) ->
    OnNomatch(State).

%% @private
-spec abstract_with(fun((gre:event()) -> term()), #state{}) -> [syntaxTree()].
abstract_with(Fun, State) when is_function(Fun, 1) ->
    abstract_getparam(Fun, fun(#state{event=Event, paramvars=Params}) ->
            {_, Fun2} = lists:keyfind(Fun, 1, Params),
            [erl_syntax:application(none, Fun2, [Event])]
        end, State).

%% @private Bind the value of a field to a variable.
%% If the value of a field has already been bound to a variable the previous
%% binding is reused over re-accessing the value. The `OnMatch' function is
%% expected to access the variable stored in the state record. The `OnNomatch'
%% function must not attempt to access the variable.
-spec abstract_getkey(atom(), nextFun(), nextFun(), #state{}) ->
        [syntaxTree()].
abstract_getkey(Key, OnMatch, OnNomatch, #state{fields=Fields}=State) ->
    case lists:keyfind(Key, 1, Fields) of
        {Key, _Variable} -> OnMatch(State);
        false -> abstract_getkey_(Key, OnMatch, OnNomatch, State)
    end.


-spec abstract_getkey_(atom(), nextFun(), nextFun(), #state{}) ->
        [syntaxTree()].
abstract_getkey_(Key, OnMatch, OnNomatch, #state{
        event=Event, fields=Fields}=State) ->
    [erl_syntax:case_expr(
        erl_syntax:application(
            erl_syntax:atom(gre), erl_syntax:atom(find),
            [erl_syntax:atom(Key), Event]),
        [erl_syntax:clause([
            erl_syntax:tuple([
                erl_syntax:atom(true),
                field_variable(Key)])], none,
             OnMatch(State#state{
                fields=[{Key, field_variable(Key)}|Fields]})),
         erl_syntax:clause([
            erl_syntax:atom(false)], none,
            OnNomatch(State))
        ]
    )].

%% @private Bind the value of a parameter to a variable.
%% During code generation the parameter value is used as the identity of the
%% parameter. At runtime a unique integer is used as the identity.
-spec abstract_getparam(term(), nextFun(), #state{}) -> [syntaxTree()].
abstract_getparam(Term, OnBound, #state{paramvars=Params}=State) ->
    case lists:keyfind(Term, 1, Params) of
        {_, _Variable} -> OnBound(State);
        %% parameter not bound to variable in this scope.
        false -> abstract_getparam_(Term, OnBound, State)
    end.


-spec abstract_getparam_(term(), nextFun(), #state{}) -> [syntaxTree()].
abstract_getparam_(Term, OnBound, #state{paramstab=Table,
        paramvars=Params}=State) ->
    Key = case ets:lookup(Table, Term) of
        [{_, Key2}] ->
            Key2;
        [] ->
            Key2 = ets:info(Table, size),
            ets:insert(Table, {Term, Key2}),
            Key2
    end,
    [erl_syntax:match_expr(
        param_variable(Key),
        erl_syntax:application(
            erl_syntax:atom(ets),
            erl_syntax:atom(lookup_element),
            [erl_syntax:application(
                erl_syntax:atom(table),
                [erl_syntax:atom(params)]),
             erl_syntax:abstract(Key),
             erl_syntax:abstract(2)]))
    ] ++ OnBound(State#state{paramvars=[{Term, param_variable(Key)}|Params]}).

%% @private Generate a variable name for the value of a field.
%% @todo Encode non-alphanumeric characters as integer values.
-spec field_variable(atom()) -> syntaxTree().
field_variable(Key) ->
    erl_syntax:variable("Field_" ++ atom_to_list(Key)).

%% @private Generate a variable name for the value of a parameter.
-spec param_variable(integer()) -> syntaxTree().
param_variable(Key) ->
    erl_syntax:variable("Param_" ++ integer_to_list(Key)).


%% @private Return an expression to increment a counter.
%% @todo Pass state record. Only Generate code if `statistics' is enabled.
-spec abstract_count(atom()) -> syntaxTree().
abstract_count(Counter) ->
    erl_syntax:application(
        erl_syntax:atom(ets),
        erl_syntax:atom(update_counter),
        [erl_syntax:application(
            erl_syntax:atom(table),
            [erl_syntax:atom(counters)]),
         erl_syntax:abstract(Counter),
         erl_syntax:abstract({2,1})]).


%% @private Return an expression to get the value of a counter.
%% @todo Pass state record. Only Generate code if `statistics' is enabled.
-spec abstract_getcount(atom()) -> [syntaxTree()].
abstract_getcount(Counter) ->
    [erl_syntax:application(
        erl_syntax:atom(ets),
        erl_syntax:atom(lookup_element),
        [erl_syntax:application(
            erl_syntax:atom(table),
            [erl_syntax:atom(counters)]),
         erl_syntax:abstract(Counter),
         erl_syntax:abstract(2)])].


%% abstract code util functions


%% @private Compile an abstract module.
-spec compile_forms(term(), [term()]) -> {ok, atom(), binary()}.
compile_forms(Forms, _Opts) ->
    case compile:forms(Forms) of
        {ok, Module, Binary} ->
            {ok, Module, Binary};
        {ok, Module, Binary, _Warnings} ->
            {ok, Module, Binary};
        Error ->
            erlang:error({compile_forms, Error})
    end.

%% @private Load a module binary.
-spec load_binary(atom(), binary()) -> {ok, loaded, atom()}.
load_binary(Module, Binary) ->
    case code:load_binary(Module, "", Binary) of
        {module, Module}  -> {ok, loaded, Module};
        {error, Reason} -> exit({error_loading_module, Module, Reason})
    end.


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

setup_query(Module, Query) ->
    ?assertNot(erlang:module_loaded(Module)),
    ?assertEqual({ok, Module}, case (catch compile(Module, Query)) of
        {'EXIT',_}=Error -> ?debugFmt("~p", [Error]), Error; Else -> Else end),
    ?assert(erlang:function_exported(Module, table, 1)),
    ?assert(erlang:function_exported(Module, handle, 1)),
    {compiled, Module}.

nullquery_compiles_test() ->
    {compiled, Mod} = setup_query(testmod1, glc:null(false)),
    ?assertError(badarg, Mod:table(noexists)).

params_table_exists_test() ->
    {compiled, Mod} = setup_query(testmod2, glc:null(false)),
    ?assert(is_integer(Mod:table(params))),
    ?assertMatch([_|_], ets:info(Mod:table(params))).

nullquery_exists_test() ->
    {compiled, Mod} = setup_query(testmod3, glc:null(false)),
    ?assert(erlang:function_exported(Mod, info, 1)),
    ?assertError(badarg, Mod:info(invalid)),
    ?assertEqual({null, false}, Mod:info('query')).

init_counters_test() ->
    {compiled, Mod} = setup_query(testmod4, glc:null(false)),
    ?assertEqual(0, Mod:info(input)),
    ?assertEqual(0, Mod:info(filter)),
    ?assertEqual(0, Mod:info(output)).

filtered_event_test() ->
    %% If no selection condition is specified no inputs can match.
    {compiled, Mod} = setup_query(testmod5, glc:null(false)),
    glc:handle(Mod, gre:make([], [list])),
    ?assertEqual(1, Mod:info(input)),
    ?assertEqual(1, Mod:info(filter)),
    ?assertEqual(0, Mod:info(output)).

nomatch_event_test() ->
    %% If a selection condition but no body is specified the event
    %% is expected to count as filtered out if the condition does
    %% not hold.
    {compiled, Mod} = setup_query(testmod6, glc:eq('$n', 'noexists@nohost')),
    glc:handle(Mod, gre:make([{'$n', 'noexists2@nohost'}], [list])),
    ?assertEqual(1, Mod:info(input)),
    ?assertEqual(1, Mod:info(filter)),
    ?assertEqual(0, Mod:info(output)).

opfilter_eq_test() ->
    %% If a selection condition but no body is specified the event
    %% counts as input to the query, but not as filtered out.
    {compiled, Mod} = setup_query(testmod7, glc:eq('$n', 'noexists@nohost')),
    glc:handle(Mod, gre:make([{'$n', 'noexists@nohost'}], [list])),
    ?assertEqual(1, Mod:info(input)),
    ?assertEqual(0, Mod:info(filter)),
    ?assertEqual(1, Mod:info(output)),
    done.


opfilter_gt_test() ->
    {compiled, Mod} = setup_query(testmod8, glc:gt(a, 1)),
    glc:handle(Mod, gre:make([{'a', 2}], [list])),
    ?assertEqual(1, Mod:info(input)),
    ?assertEqual(0, Mod:info(filter)),
    glc:handle(Mod, gre:make([{'a', 0}], [list])),
    ?assertEqual(2, Mod:info(input)),
    ?assertEqual(1, Mod:info(filter)),
    ?assertEqual(1, Mod:info(output)),
    done.

opfilter_lt_test() ->
    {compiled, Mod} = setup_query(testmod9, glc:lt(a, 1)),
    glc:handle(Mod, gre:make([{'a', 0}], [list])),
    ?assertEqual(1, Mod:info(input)),
    ?assertEqual(0, Mod:info(filter)),
    ?assertEqual(1, Mod:info(output)),
    glc:handle(Mod, gre:make([{'a', 2}], [list])),
    ?assertEqual(2, Mod:info(input)),
    ?assertEqual(1, Mod:info(filter)),
    ?assertEqual(1, Mod:info(output)),
    done.

allholds_op_test() ->
    {compiled, Mod} = setup_query(testmod10,
        glc:all([glc:eq(a, 1), glc:eq(b, 2)])),
    glc:handle(Mod, gre:make([{'a', 1}], [list])),
    glc:handle(Mod, gre:make([{'a', 2}], [list])),
    ?assertEqual(2, Mod:info(input)),
    ?assertEqual(2, Mod:info(filter)),
    glc:handle(Mod, gre:make([{'b', 1}], [list])),
    glc:handle(Mod, gre:make([{'b', 2}], [list])),
    ?assertEqual(4, Mod:info(input)),
    ?assertEqual(4, Mod:info(filter)),
    glc:handle(Mod, gre:make([{'a', 1},{'b', 2}], [list])),
    ?assertEqual(5, Mod:info(input)),
    ?assertEqual(4, Mod:info(filter)),
    ?assertEqual(1, Mod:info(output)),
    done.

anyholds_op_test() ->
    {compiled, Mod} = setup_query(testmod11,
        glc:any([glc:eq(a, 1), glc:eq(b, 2)])),
    glc:handle(Mod, gre:make([{'a', 2}], [list])),
    glc:handle(Mod, gre:make([{'b', 1}], [list])),
    ?assertEqual(2, Mod:info(input)),
    ?assertEqual(2, Mod:info(filter)),
    glc:handle(Mod, gre:make([{'a', 1}], [list])),
    glc:handle(Mod, gre:make([{'b', 2}], [list])),
    ?assertEqual(4, Mod:info(input)),
    ?assertEqual(2, Mod:info(filter)),
    done.

with_function_test() ->
    Self = self(),
    {compiled, Mod} = setup_query(testmod12,
        glc:with(glc:eq(a, 1), fun(Event) -> Self ! gre:fetch(a, Event) end)),
    glc:handle(Mod, gre:make([{a,1}], [list])),
    ?assertEqual(1, Mod:info(output)),
    ?assertEqual(1, receive Msg -> Msg after 0 -> notcalled end),
    done.

-endif.
