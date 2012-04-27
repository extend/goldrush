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

%% @doc Query processing functions.
-module(glc_lib).

-export([
    reduce/1
]).

%% @doc Return a reduced version of a query.
%% 
%% The purpose of this function is to ensure that a query filter
%% is in the simplest possible form. The query filter returned
%% from this function is functionally equivalent to the original.
reduce(Query) ->
    repeat(Query, fun(Q0) ->
        Q1 = flatten(Q0),
        Q2 = required(Q1),
        Q3 = flatten(Q2),
        Q4 = common(Q3),
        Q4
    end).

%% @private Repeatedly apply a function to a query.
%% This is used for query transformation functions 
%% applied multiple times 
repeat(Query, Fun) ->
    case Fun(Query) of
        Query -> Query;
        Query2 -> repeat(Query2, Fun)
    end.

%% @private Flatten a condition tree.
flatten({all, [Cond]}) ->
    Cond;
flatten({any, [Cond]}) ->
    Cond;
flatten({all, Conds}) ->
    flatten_all([flatten(Cond) || Cond <- Conds]);
flatten({any, [_|_]=Conds}) ->
    flatten_any([flatten(Cond) || Cond <- Conds]);
flatten({with, Cond, Action}) ->
    {with, flatten(Cond), Action};
flatten(Other) ->
    return_valid(Other).


%% @private Flatten and remove duplicate members of an "all" filter.
flatten_all(Conds) ->
    {all, lists:usort(flatten_all_(Conds))}.

flatten_all_([{all, Conds}|T]) ->
    Conds ++ flatten_all_(T);
flatten_all_([H|T]) ->
    [H|flatten_all_(T)];
flatten_all_([]) ->
    [].

%% @private Flatten and remove duplicate members of an "any" filter.
flatten_any(Conds) ->
    {any, lists:usort(flatten_any_(Conds))}.

flatten_any_([{any, Conds}|T]) ->
    Conds ++ flatten_any_(T);
flatten_any_([H|T]) ->
    [H|flatten_any_(T)];
flatten_any_([]) ->
    [].

%% @private Factor out required filters.
%%
%% Identical conditions may occur in all sub-filters of an "any" filter. These
%% filters can be tested once before testing the conditions that are unique to
%% each sub-filter.
%%
%% Assume that the input has been flattened first in order to eliminate all
%% occurances of an "any" filters being "sub-filters" of "any" filters.
required({any, [H|_]=Conds}) ->
    Init = ordsets:from_list(case H of {all, Init2} -> Init2; H -> [H] end),
    case required(Conds, Init) of
        [] ->
            Conds2 = [required(Cond) || Cond <- Conds],
            {any, Conds2};
        [_|_]=Req ->
            Conds2 = [required(deleteall(Cond, Req)) || Cond <- Conds],
            {all, [{all, Req}, {any, Conds2}]}
    end;
required({all, Conds}) ->
    {all, [required(Cond) || Cond <- Conds]};
required(Other) ->
    Other.

required([{all, Conds}|T], Acc) ->
    required(T, ordsets:intersection(ordsets:from_list(Conds), Acc));
required([{any, _}|_]=Cond, Acc) ->
    erlang:error(badarg, [Cond, Acc]);
required([H|T], Acc) ->
    required(T, ordsets:intersection(ordsets:from_list([H]), Acc));
required([], Acc) ->
    Acc.

%% @private Factor our common filters.
%%
%% Identical conditions may occur in some sub-filters of an "all" filter. These
%% filters can be tested once before testing the conditions that are unique to
%% each sub-filter. This is different from factoring out common sub-filters
%% in an "any" filter where the only those sub-filters that exist in all
%% members.
%%
%% Assume that the input has been flattened first in order to eliminate all
%% occurances of an "any" filters being "sub-filters" of "any" filters.
common({all, Conds}) ->
    case common_(Conds, []) of
        {found, Found} ->
            {all, [Found|[delete(Cond, Found) || Cond <- Conds]]};
        nonefound ->
            {all, [common(Cond) || Cond <- Conds]}
    end;
common({any, Conds}) ->
    {any, [common(Cond) || Cond <- Conds]};
common(Other) ->
    Other.
    

common_([{any, Conds}|T], Seen) ->
    Set = ordsets:from_list(Conds),
    case ordsets:intersection(Set, Seen) of
        [] -> common_(T, ordsets:union(Set, Seen));
        [H|_] -> {found, H}
    end;
common_([H|T], Seen) ->
    case ordsets:is_element(H, Seen) of
        false -> common_(T, ordsets:union(ordsets:from_list([H]), Seen));
        true -> {found, H}
    end;
common_([], _Seen) ->
    nonefound.
    



%% @private Delete all occurances of a filter.
%%
%% Assume that the function is called because a filter is tested
%% by a parent filter. It is therefore safe to replace occurances
%% with a null filter that always returns true.
delete({all, Conds}, Filter) ->
    {all, [delete(Cond, Filter) || Cond <- Conds, Cond =/= Filter]};
delete({any, Conds}, Filter) ->
    {any, [delete(Cond, Filter) || Cond <- Conds, Cond =/= Filter]};
delete(Filter, Filter) ->
    {null, true};
delete(Cond, _Filter) ->
    Cond.

%% @private Delete all occurances of multiple filters.
deleteall(Filter, [H|T]) ->
    deleteall(delete(Filter, H), T);
deleteall(Filter, []) ->
    Filter.



%% @private Test if a term is a valid filter.
is_valid({Field, '<', _Term}) when is_atom(Field) ->
    true;
is_valid({Field, '=', _Term}) when is_atom(Field) ->
    true;
is_valid({Field, '>', _Term}) when is_atom(Field) ->
    true;
is_valid({null, true}) ->
    true;
is_valid({null, false}) ->
    true;
is_valid(_Other) ->
    false.

%% @private Assert that a term is a valid filter.
%% If the term is a valid filter. The original term will be returned.
%% If the term is not a valid filter. A `badarg' error is thrown.
return_valid(Term) ->
    case is_valid(Term) of
        true -> Term;
        false ->
            io:format(user, "~w~n", [Term]),
            erlang:error(badarg, [Term])
    end.


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

all_one_test() ->
    ?assertEqual(glc:eq(a, 1),
        glc_lib:reduce(glc:all([glc:eq(a, 1)]))
    ).

all_sort_test() ->
    ?assertEqual(glc:all([glc:eq(a, 1), glc:eq(b, 2)]),
        glc_lib:reduce(glc:all([glc:eq(b, 2), glc:eq(a, 1)]))
    ).

any_one_test() ->
    ?assertEqual(glc:eq(a, 1),
        glc_lib:reduce(glc:any([glc:eq(a, 1)]))
    ).

any_sort_test() ->
    ?assertEqual(glc:any([glc:eq(a, 1), glc:eq(b, 2)]),
        glc_lib:reduce(glc:any([glc:eq(b, 2), glc:eq(a, 1)]))
    ).

all_nest_test() ->
    ?assertEqual(glc:all([glc:eq(a, 1), glc:eq(b, 2)]),
        glc_lib:reduce(glc:all([glc:eq(a, 1), glc:all([glc:eq(b, 2)])]))
    ),
    ?assertEqual(glc:all([glc:eq(a, 1), glc:eq(b, 2), glc:eq(c, 3)]),
        glc_lib:reduce(glc:all([glc:eq(c, 3),
            glc:all([glc:eq(a, 1),
                glc:all([glc:eq(b, 2)])])]))
    ).

any_nest_test() ->
    ?assertEqual(glc:any([glc:eq(a, 1), glc:eq(b, 2)]),
        glc_lib:reduce(glc:any([glc:eq(a, 1), glc:any([glc:eq(b, 2)])]))
    ),
    ?assertEqual(glc:any([glc:eq(a, 1), glc:eq(b, 2), glc:eq(c, 3)]),
        glc_lib:reduce(glc:any([glc:eq(c, 3),
            glc:any([glc:eq(a, 1),
                glc:any([glc:eq(b, 2)])])]))
    ).

all_equiv_test() ->
    ?assertEqual(glc:eq(a, 1),
        glc_lib:reduce(glc:all([glc:eq(a, 1), glc:eq(a, 1)]))
    ).

any_equiv_test() ->
    ?assertEqual(glc:eq(a, 1),
        glc_lib:reduce(glc:any([glc:eq(a, 1), glc:eq(a, 1)]))
    ).

any_required_test() ->
    ?assertEqual(
        glc:all([
            glc:any([glc:eq(b, 2), glc:eq(c, 3)]),
            glc:eq(a, 1)
        ]),
        glc_lib:reduce(
            glc:any([
                glc:all([glc:eq(a, 1), glc:eq(b, 2)]),
                glc:all([glc:eq(a, 1), glc:eq(c, 3)])]))
    ).
        

all_common_test() ->
    ?assertEqual(
        glc:all([glc:eq(a, 1), glc:eq(b, 2), glc:eq(c, 3)]),
        glc_lib:reduce(
            glc:all([
                glc:any([glc:eq(a, 1), glc:eq(b, 2)]),
                glc:any([glc:eq(a, 1), glc:eq(c, 3)])]))
    ).

delete_from_all_test() ->
    ?assertEqual(
        glc:all([glc:eq(b,2)]),
        deleteall(
            glc:all([glc:eq(a, 1),glc:eq(b,2)]), [glc:eq(a, 1)])
    ).

delete_from_any_test() ->
    ?assertEqual(
        glc:any([glc:eq(b,2)]),
        deleteall(
            glc:any([glc:eq(a, 1),glc:eq(b,2)]), [glc:eq(a, 1)])
    ).

-endif.
